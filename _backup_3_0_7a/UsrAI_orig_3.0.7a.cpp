#include "UsrAI.h"
#include<set>
#include <iostream>
#include<unordered_map>
#include<list>
#include <cstdlib>
#include <cmath>

using namespace std;
tagGame tagUsrGame;
ins UsrIns;
/*##########DO NOT MODIFY THE CODE ABOVE##########*/

void UsrAI::processData()
{
    tagInfo info = getInfo();
    controlEconomy(info);    // 经济：造村民 + 派工
    controlBuilding(info);   // 建筑：建造顺序 + 升铜器
    controlMilitary(info);   // 军事：训练 + 防守 + 反攻
    controlPriest(info);     // 祭司：转化 / 治疗 / 回退
}

// 己方祭司 SN
int UsrAI::findPriestSN(const tagInfo& info)
{
    for (const auto& a : info.armies)
        if (a.Sort == AT_PRIEST) return a.SN;
    return -1;
}

// 敌人（军队/农民/建筑）细节坐标
bool UsrAI::enemyDetailPos(const tagInfo& info, int SN, double& dr, double& ur)
{
    const double BLOCK = double(BLOCKSIDELENGTH);
    for (const auto& a : info.enemy_armies)  if (a.SN == SN) { dr = a.DR; ur = a.UR; return true; }
    for (const auto& f : info.enemy_farmers) if (f.SN == SN) { dr = f.DR; ur = f.UR; return true; }
    for (const auto& b : info.enemy_buildings) if (b.SN == SN) {
        dr = (b.BlockDR + 0.5) * BLOCK; ur = (b.BlockUR + 0.5) * BLOCK; return true;
    }
    return false;
}

// 最近敌人 SN（军队/农民/建筑，取欧氏距离最小）
int UsrAI::nearestEnemySN(const tagInfo& info, double pr, double pu, double& outDist)
{
    const double BLOCK = double(BLOCKSIDELENGTH);
    int best = -1; double bd = 1e18;
    for (const auto& a : info.enemy_armies) {
        double d = calDistance(pr, pu, a.DR, a.UR);
        if (d < bd) { bd = d; best = a.SN; }
    }
    for (const auto& f : info.enemy_farmers) {
        double d = calDistance(pr, pu, f.DR, f.UR);
        if (d < bd) { bd = d; best = f.SN; }
    }
    for (const auto& b : info.enemy_buildings) {
        double d = calDistance(pr, pu, (b.BlockDR + 0.5) * BLOCK, (b.BlockUR + 0.5) * BLOCK);
        if (d < bd) { bd = d; best = b.SN; }
    }
    outDist = bd;
    return best;
}

// 最近敌人单位 SN（仅军队/农民，不含建筑）——用于祭司日常转化
int UsrAI::nearestEnemyUnitSN(const tagInfo& info, double pr, double pu, double& outDist)
{
    int best = -1; double bd = 1e18;
    for (const auto& a : info.enemy_armies) {
        double d = calDistance(pr, pu, a.DR, a.UR);
        if (d < bd) { bd = d; best = a.SN; }
    }
    for (const auto& f : info.enemy_farmers) {
        double d = calDistance(pr, pu, f.DR, f.UR);
        if (d < bd) { bd = d; best = f.SN; }
    }
    outDist = bd;
    return best;
}
int UsrAI::findAttackerSN(const tagInfo& info, int priestSN)
{
    for (const auto& a : info.enemy_armies)  if (a.WorkObjectSN == priestSN) return a.SN;
    for (const auto& f : info.enemy_farmers) if (f.WorkObjectSN == priestSN) return f.SN;
    return -1;
}

// 血量百分比最低的残血友军 SN（不含祭司本人）
int UsrAI::findWoundedAllySN(const tagInfo& info, int priestSN)
{
    int best = -1; double br = 1e18;
    auto consider = [&](int sn, int blood, int maxblood) {
        if (sn == priestSN || maxblood <= 0 || blood >= maxblood) return;
        double ratio = double(blood) / double(maxblood);
        if (ratio < br) { br = ratio; best = sn; }
    };
    for (const auto& a : info.armies)  consider(a.SN, a.Blood, a.MaxBlood);
    for (const auto& f : info.farmers) consider(f.SN, f.Blood, f.MaxBlood);
    return best;
}

// 市镇中心块坐标（回退/躲避的锚点）
bool UsrAI::centerBlockPos(const tagInfo& info, int& bdr, int& bur)
{
    for (const auto& b : info.buildings)
        if (b.Type == BUILDING_CENTER) { bdr = b.BlockDR; bur = b.BlockUR; return true; }
    return false;
}

// 祭司状态机（每帧由 processData 调用）
void UsrAI::controlPriest(const tagInfo& info)
{
    const double BLOCK = double(BLOCKSIDELENGTH);
    const double CONVERT_RANGE = 12 * BLOCK;   // 转化射程 = 安全距离
    const double APPROACH_DIST = 10 * BLOCK;   // 逼近到 10 格，留余量不贴脸

    int priestSN = findPriestSN(info);
    if (priestSN < 0) return;
    const tagArmy* priest = nullptr;
    for (const auto& a : info.armies) if (a.SN == priestSN) { priest = &a; break; }
    if (!priest) return;

    // 1. 低血回退（最高优先级，打断一切）
    if (priest->Blood < 30) {
        int bdr = 0, bur = 0;
        if (centerBlockPos(info, bdr, bur))
            HumanMove(priestSN, (bdr + 0.5) * BLOCK, (bur + 0.5) * BLOCK);
        return;
    }

    // 2. 正在转化/攻击（施法 2~6 秒）中，不打扰，避免打断施法
    if (priest->NowState == HUMAN_STATE_ATTACKING) return;

    int attacker = findAttackerSN(info, priestSN);
    double nd = 1e18;
    int nearestUnit = nearestEnemyUnitSN(info, priest->DR, priest->UR, nd);  // 只找单位，不碰建筑
    bool hasEnemy = (attacker >= 0 || nearestUnit >= 0);

    // 3. 冷却好 + 有敌人 → 转化（只转化单位）
    if (hasEnemy && priest->ConvertCooldown <= 0) {
        int target = attacker;                                    // 优先转化正在攻击自己的敌人
        if (target < 0 && nearestUnit >= 0 && nd <= CONVERT_RANGE) // 其次转化射程内最近单位
            target = nearestUnit;
        if (target >= 0) {
            HumanAction(priestSN, target);
        } else {
            // 单位都超出射程：逼近最近单位到 10 格
            double edr = 0, eur = 0;
            if (enemyDetailPos(info, nearestUnit, edr, eur)) {
                double dx = edr - priest->DR, dy = eur - priest->UR;
                double d = sqrt(dx * dx + dy * dy);
                if (d > CONVERT_RANGE && d > 1.0) {
                    double k = (d - APPROACH_DIST) / d;
                    HumanMove(priestSN, priest->DR + dx * k, priest->UR + dy * k);
                }
            }
        }
        return;
    }

    // 4. 冷却中 + 有敌人 → 保持安全距离（后撤，不治疗）
    if (hasEnemy) {
        double nd2 = 1e18;
        int nearestAny = nearestEnemySN(info, priest->DR, priest->UR, nd2);  // 含建筑，用于判断危险
        if (nearestAny >= 0 && nd2 < CONVERT_RANGE) {
            double edr = 0, eur = 0;
            if (enemyDetailPos(info, nearestAny, edr, eur)) {
                double dx = priest->DR - edr, dy = priest->UR - eur;  // 远离敌人的方向
                double d = sqrt(dx * dx + dy * dy);
                if (d > 1.0) {
                    double k = (CONVERT_RANGE - nd2) / d;   // 后撤到安全距离边缘（不加多余偏移）
                    double nx = priest->DR + dx * k;
                    double ny = priest->UR + dy * k;
                    // 边界钳制，防止撤出地图
                    if (nx < 0) nx = 0;
                    if (ny < 0) ny = 0;
                    if (nx > (MAP_L - 1) * BLOCK) nx = (MAP_L - 1) * BLOCK;
                    if (ny > (MAP_U - 1) * BLOCK) ny = (MAP_U - 1) * BLOCK;
                    HumanMove(priestSN, nx, ny);
                }
            }
        }
        return;
    }

    // 5. 无敌人：治疗中不打扰（治疗是 WORKING 状态）
    if (priest->NowState == HUMAN_STATE_WORKING) return;

    // 6. 无敌人：治疗残血友军（战后治疗）
    int wounded = findWoundedAllySN(info, priestSN);
    if (wounded >= 0) {
        HumanAction(priestSN, wounded);
        return;
    }

    // 7. 无敌人且无人可治 → 反攻阶段跟随推进，否则待命
    if (info.GameFrame > 21000) {
        double edr = 0, eur = 0;
        if (enemySiegePos(info, edr, eur)) {
            HumanMove(priestSN, edr, eur);
        } else {
            int cdr = 0, cur = 0;
            if (centerBlockPos(info, cdr, cur))
                HumanMove(priestSN, (MAP_L - 1 - cdr + 0.5) * BLOCK, (MAP_U - 1 - cur + 0.5) * BLOCK);
        }
    }
}

// ==================== 经济调度 ====================

// 资源大类匹配：0=食物 1=木头 2=石头 3=黄金
static bool matchResourceClass(int resType, int resClass)
{
    switch (resClass) {
    case 0: return resType == RESOURCE_BUSH || resType == RESOURCE_GAZELLE ||
                    resType == RESOURCE_ELEPHANT || resType == RESOURCE_LION ||
                    resType == RESOURCE_FISH;
    case 1: return resType == RESOURCE_TREE;
    case 2: return resType == RESOURCE_STONE;
    case 3: return resType == RESOURCE_GOLD;
    }
    return false;
}

// 陆地村民数量
int UsrAI::countFarmers(const tagInfo& info)
{
    int n = 0;
    for (const auto& f : info.farmers)
        if (f.FarmerSort == FARMERTYPE_FARMER) n++;
    return n;
}

// 指定类型建筑数量（含建造中）
int UsrAI::countBuilding(const tagInfo& info, int type)
{
    int n = 0;
    for (const auto& b : info.buildings)
        if (b.Type == type) n++;
    return n;
}

// 已建成（Percent>=100）建筑数量——用于时代升级前置等需要"建成"的判断
int UsrAI::countBuildingBuilt(const tagInfo& info, int type)
{
    int n = 0;
    for (const auto& b : info.buildings)
        if (b.Type == type && b.Percent >= 100) n++;
    return n;
}

// 最近有存粮的农田 SN（供村民种田采食）
int UsrAI::nearestFarmSN(const tagInfo& info, double pr, double pu)
{
    const double BLOCK = double(BLOCKSIDELENGTH);
    int best = -1; double bd = 1e18;
    for (const auto& b : info.buildings) {
        if (b.Type != BUILDING_FARM || b.Percent < 100) continue;
        if (b.Cnt <= 0) continue;   // 农田已耗尽
        double d = calDistance(pr, pu, (b.BlockDR + 0.5) * BLOCK, (b.BlockUR + 0.5) * BLOCK);
        if (d < bd) { bd = d; best = b.SN; }
    }
    return best;
}

// 最近的可采集资源
int UsrAI::nearestResourceSN(const tagInfo& info, double pr, double pu, int resClass)
{
    int best = -1; double bd = 1e18;
    for (const auto& r : info.resources) {
        if (!matchResourceClass(r.Type, resClass)) continue;
        if (r.Cnt <= 0 && r.Blood <= 0) continue;   // 已采空且无血（动物消失）
        double d = calDistance(pr, pu, r.DR, r.UR);
        if (d < bd) { bd = d; best = r.SN; }
    }
    return best;
}

// 轮询分配资源大类（按时代调整比例）
int UsrAI::pickResourceClass(const tagInfo& info, int idx)
{
    int r = idx % 10;
    if (info.civilizationStage >= CIVILIZATION_BRONZEAGE) {
        // 铜器：食物4 黄金3 木头2 石头1（黄金是建军瓶颈）
        if (r < 4) return 0;
        if (r < 7) return 3;
        if (r < 9) return 1;
        return 2;
    }
    // 工具：食物6 木头3 石头1
    if (r < 6) return 0;
    if (r < 9) return 1;
    return 2;
}

// 造村民 + 空闲村民派工
void UsrAI::controlEconomy(const tagInfo& info)
{
    int farmers = countFarmers(info);
    int target = (info.civilizationStage >= CIVILIZATION_BRONZEAGE) ? 24 : 20;

    // 1. 市镇中心产村民
    for (const auto& b : info.buildings) {
        if (b.Type == BUILDING_CENTER && b.Percent >= 100 && b.Project == ACT_NULL
            && farmers < target && info.Human_Num < info.Human_MaxNum && info.Meat >= 50) {
            BuildingAction(b.SN, BUILDING_CENTER_CREATEFARMER);
        }
    }

    // 2. 空闲村民派工
    int idx = 0;
    for (const auto& f : info.farmers) {
        if (f.FarmerSort != FARMERTYPE_FARMER || f.NowState != HUMAN_STATE_IDLE) continue;
        int cls = pickResourceClass(info, idx);
        int sn = -1;
        if (cls == 0) {
            // 食物：优先去有存粮的农田，其次浆果/猎物
            sn = nearestFarmSN(info, f.DR, f.UR);
            if (sn < 0) sn = nearestResourceSN(info, f.DR, f.UR, 0);
        } else {
            sn = nearestResourceSN(info, f.DR, f.UR, cls);
        }
        if (sn >= 0) HumanAction(f.SN, sn);
        idx++;
    }
}

// 判断 size×size 区域是否为已探索的平坦草地（高度一致）
bool UsrAI::isFlatArea(const tagInfo& info, int bdr, int bur, int size)
{
    if (info.theMap == nullptr) return false;
    if (bdr < 0 || bur < 0 || bdr + size > MAP_L || bur + size > MAP_U) return false;
    int h = -1;
    for (int i = bdr; i < bdr + size; i++) {
        for (int j = bur; j < bur + size; j++) {
            const tagTerrain& t = (*info.theMap)[i][j];
            if (t.type != MAPPATTERN_GRASS) return false;   // 未探索或非草地
            if (h < 0) h = t.height;
            else if (t.height != h) return false;           // 高度必须一致
        }
    }
    return true;
}

// 找可建造平地（螺旋搜索，排除重叠与上次失败位置）
bool UsrAI::findBuildPos(const tagInfo& info, int buildNum, int& bdr, int& bur)
{
    static int lastDR = -1, lastUR = -1, lastSize = -1;
    int size = (buildNum == BUILDING_HOME) ? 2 : 3;
    int cdr = 0, cur = 0;
    if (!centerBlockPos(info, cdr, cur)) return false;

    // 候选区域是否与已有建筑/单位重叠（建筑 BlockDR/BlockUR 为占地下角，向右上扩展）
    auto occupied = [&](int i, int j) -> bool {
        for (const auto& b : info.buildings) {
            int bs = (b.Type == BUILDING_HOME || b.Type == BUILDING_ARROWTOWER) ? 2 : 3;
            if (i < b.BlockDR + bs && b.BlockDR < i + size &&
                j < b.BlockUR + bs && b.BlockUR < j + size) return true;
        }
        for (const auto& f : info.farmers)
            if (i <= f.BlockDR && f.BlockDR < i + size && j <= f.BlockUR && f.BlockUR < j + size) return true;
        for (const auto& a : info.armies)
            if (i <= a.BlockDR && a.BlockDR < i + size && j <= a.BlockUR && a.BlockUR < j + size) return true;
        return false;
    };

    for (int r = 2; r <= 24; r++) {
        for (int i = cdr - r; i <= cdr + r; i++) {
            for (int j = cur - r; j <= cur + r; j++) {
                if (!isFlatArea(info, i, j, size)) continue;
                if (occupied(i, j)) continue;                          // 排除重叠
                if (i == lastDR && j == lastUR && size == lastSize) continue;  // 跳过上次失败位
                bdr = i; bur = j;
                lastDR = i; lastUR = j; lastSize = size;
                return true;
            }
        }
    }
    return false;
}

// 建筑顺序 + 升铜器
void UsrAI::controlBuilding(const tagInfo& info)
{
    auto tryBuild = [&](int buildNum) -> bool {
        int bdr = 0, bur = 0;
        if (!findBuildPos(info, buildNum, bdr, bur)) return false;
        for (const auto& f : info.farmers) {
            if (f.FarmerSort == FARMERTYPE_FARMER && f.NowState == HUMAN_STATE_IDLE) {
                HumanBuild(f.SN, buildNum, bdr, bur);
                return true;
            }
        }
        return false;
    };

    // 1. 房屋（人口余量 ≤ 2，上限 12 座）
    if (info.Human_MaxNum - info.Human_Num <= 2 && countBuilding(info, BUILDING_HOME) < 12 && info.Wood >= 30)
        tryBuild(BUILDING_HOME);

    // 2. 兵营（开局没有）
    if (countBuilding(info, BUILDING_ARMYCAMP) < 1 && info.Wood >= 125)
        tryBuild(BUILDING_ARMYCAMP);

    // 3. 箭塔科技：谷仓研发「建造箭塔」（一次性，50 食物，工具时代尽早）
    if (!towerResearched) {
        for (const auto& b : info.buildings) {
            if (b.Type == BUILDING_GRANARY && b.Percent >= 100 && b.Project == ACT_NULL && info.Meat >= 50) {
                BuildingAction(b.SN, BUILDING_GRANARY_ARROWTOWER);
                towerResearched = true;
            }
        }
    }

    // 4. 箭塔（150 石头，含开局 1 座共 3 座，工具时代防守主力）
    if (towerResearched && countBuildingBuilt(info, BUILDING_ARROWTOWER) < 3 && info.Stone >= 150)
        tryBuild(BUILDING_ARROWTOWER);

    // 5. 市场（升铜器前置）
    if (countBuilding(info, BUILDING_MARKET) < 1 && info.Wood >= 150)
        tryBuild(BUILDING_MARKET);

    // 6. 马厩（第 2 座工具时代建筑，升铜器前置）
    if (countBuilding(info, BUILDING_MARKET) >= 1 && countBuilding(info, BUILDING_STABLE) < 1 && info.Wood >= 150)
        tryBuild(BUILDING_STABLE);

    // 7. 农场（市场建成后，75 木头，共 4 座）
    if (countBuildingBuilt(info, BUILDING_MARKET) >= 1 && countBuilding(info, BUILDING_FARM) < 4 && info.Wood >= 75)
        tryBuild(BUILDING_FARM);

    // 8. 升铜器：2 座「已建成」的工具时代建筑 + 800 食物
    int toolB = countBuildingBuilt(info, BUILDING_MARKET) + countBuildingBuilt(info, BUILDING_STABLE)
              + countBuildingBuilt(info, BUILDING_RANGE);
    if (info.civilizationStage == CIVILIZATION_TOOLAGE && toolB >= 2 && info.Meat >= 800) {
        for (const auto& b : info.buildings)
            if (b.Type == BUILDING_CENTER && b.Percent >= 100 && b.Project == ACT_NULL)
                BuildingAction(b.SN, BUILDING_CENTER_UPGRADE);
    }

    // 9. 铜器：学院（方阵兵）
    if (info.civilizationStage >= CIVILIZATION_BRONZEAGE && countBuilding(info, BUILDING_COLLAGE) < 1 && info.Wood >= 180)
        tryBuild(BUILDING_COLLAGE);
}

// ==================== 军事调度 ====================

// 非祭司军队数量
int UsrAI::countArmy(const tagInfo& info)
{
    int n = 0;
    for (const auto& a : info.armies) if (a.Sort != AT_PRIEST) n++;
    return n;
}

// 敌方攻城武器厂坐标（已探索）
bool UsrAI::enemySiegePos(const tagInfo& info, double& dr, double& ur)
{
    const double BLOCK = double(BLOCKSIDELENGTH);
    for (const auto& b : info.enemy_buildings)
        if (b.Type == BUILDING_SIEGE) { dr = (b.BlockDR + 0.5) * BLOCK; ur = (b.BlockUR + 0.5) * BLOCK; return true; }
    return false;
}

// 训练 + 防守 + 反攻
void UsrAI::controlMilitary(const tagInfo& info)
{
    // 1. 训练
    if (info.civilizationStage == CIVILIZATION_TOOLAGE && info.GameFrame > 2500) {
        // 工具时代：兵营产棍棒兵（第一波防守）
        for (const auto& b : info.buildings)
            if (b.Type == BUILDING_ARMYCAMP && b.Percent >= 100 && b.Project == ACT_NULL
                && info.Meat >= 50 && info.Human_Num < info.Human_MaxNum)
                BuildingAction(b.SN, BUILDING_ARMYCAMP_CREATE_CLUBMAN);
    } else if (info.civilizationStage >= CIVILIZATION_BRONZEAGE) {
        // 铜器：学院产方阵（核心肉盾）+ 兵营产棍棒（辅助）
        for (const auto& b : info.buildings)
            if (b.Type == BUILDING_COLLAGE && b.Percent >= 100 && b.Project == ACT_NULL
                && info.Meat >= 60 && info.Gold >= 40 && info.Human_Num < info.Human_MaxNum)
                BuildingAction(b.SN, BUILDING_COLLAGE_CREATE_HOPLITE);
        for (const auto& b : info.buildings)
            if (b.Type == BUILDING_ARMYCAMP && b.Percent >= 100 && b.Project == ACT_NULL
                && info.Meat >= 50 && info.Human_Num < info.Human_MaxNum)
                BuildingAction(b.SN, BUILDING_ARMYCAMP_CREATE_CLUBMAN);
    }

    // 2. 防守 / 反攻
    bool offense = (info.GameFrame > 21000);   // 第三波后转入反攻
    double targetDR = 0, targetUR = 0;
    bool hasTarget = false;
    if (offense) {
        if (enemySiegePos(info, targetDR, targetUR)) {
            hasTarget = true;
        } else {
            int cdr = 0, cur = 0;
            if (centerBlockPos(info, cdr, cur)) {
                targetDR = (MAP_L - 1 - cdr + 0.5) * double(BLOCKSIDELENGTH);
                targetUR = (MAP_U - 1 - cur + 0.5) * double(BLOCKSIDELENGTH);
                hasTarget = true;
            }
        }
    }

    for (const auto& a : info.armies) {
        if (a.Sort == AT_PRIEST) continue;   // 祭司由 controlPriest 处理
        if (a.NowState != HUMAN_STATE_IDLE) continue;

        if (offense) {
            // 反攻：优先攻击视野内敌人（含建筑），无敌人则向目标推进
            double nd = 1e18;
            int enemy = nearestEnemySN(info, a.DR, a.UR, nd);
            if (enemy >= 0) HumanAction(a.SN, enemy);
            else if (hasTarget) HumanMove(a.SN, targetDR, targetUR);
        } else {
            // 防守：攻击视野内最近敌人
            double nd = 1e18;
            int enemy = nearestEnemySN(info, a.DR, a.UR, nd);
            if (enemy >= 0) HumanAction(a.SN, enemy);
        }
    }
}
