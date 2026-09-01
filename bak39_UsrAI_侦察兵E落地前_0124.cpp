#include "UsrAI.h"
#include<set>
#include <iostream>
#include<unordered_map>
#include<list>
#include <cstdlib>
#include <cmath>
#include <vector>
#include <algorithm>
using namespace std;
tagGame tagUsrGame;
ins UsrIns;
/*##########DO NOT MODIFY THE CODE ABOVE##########*/
// ==================== 本帧指令防冲突（每帧 clear） ====================
static std::set<int> g_assigned;              // 本帧已派过指令的单位 SN（农民/建筑）
static std::set<int> g_buildAssigned;         // 本帧已派去建造的农民 SN（防同帧多个 tryBuild 抢同一农民）
static std::set<int> g_farmAssigned;          // 本帧已派工种田的农田 SN（防同帧双人种一块）
static int g_jobRound = 0;                    // 农民工种轮询游标（跨帧持续递增，防全员漂移到食物）
static std::map<int,int> g_farmerTargetSN;    // 村民 SN -> 上次工作目标 SN（跨帧锁定，资源耗尽才换）
static std::map<int,int> g_buildDispatch;     // 建筑类型 -> 已派去建造该类型的农民 SN（跨帧防抢建）
static bool g_swordResearched = false;        // 战斧科技（工具时代）已下发研发
static bool g_meleeResearched = false;        // 仓库近战+2 科技（工具时代）已下发研发
static bool g_towerUpgradeResearched = false; // 铜器时代箭塔强化已下发研发
static bool g_logisticsResearched = false;    // 铜器时代兵营后勤已下发研发
static bool g_wheelResearched = false;        // 车轮科技（市场，解锁战车弓）已下发研发
static bool g_compositeResearched = false;    // 复合弓科技（靶场，解锁复合弓）已确认研发完成
static bool g_woodUpgradeResearched = false;  // 木材加工（市场，远程攻击距离+1&伐木+2）已下发研发
// 科技研发观察状态（跨帧）：指令下发后必须观察到"Project 进入研发 → 释放"才算研发成功。
// 防止"研发指令被引擎拒绝（如资源被同帧其他指令抢走）但标志已置位"→ 后续训练被锁刷屏（错误码 12）
struct TechWatch { bool researching = false; int frame = -100000; };
static TechWatch g_watchComposite, g_watchWheel, g_watchLogistics;
static bool g_underAttack = false;            // 战斗状态：敌军进入基地 15 格内（村民反击触发）
// ==================== 农田所有权锁定（一田一农） ====================
static std::map<int,int> g_farmerFarm;    // 农民 SN -> 锁定的农田 SN（跨帧持久，含战斗/交粮往返）
static std::set<int>     g_ownedFarms;    // 已被锁定的农田 SN 集合（nearestFarmSN 快速跳过）
// ==================== 粮食预警阈值 ====================
static const int FOOD_ALERT_THRESHOLD = 120;   // 粮食低于此值：加码采食 + 紧急建农场
static void pruneFarmLeases(const tagInfo& info);   // 前置声明（定义在下方）
// ==================== 第三波决策相关常量 ====================
// 敌方波次（与 enemyai.cpp 的 #define 对齐）：第一波 6000 / 第二波 13500 / 第三波 21000
static const int WAVE3_FRAME = 21000;
// 箭塔射程(格)——与 config.json "DIS_ARROWTOWER": 7 一致。敌人进入此范围即由箭塔自动输出，
// 我方单位负责"拉仇恨"（敌方 FindWaveTargetByPriority 优先攻击打自己的对象）。
static const int ARROWTOWER_RANGE_BLOCKS = 7;
// 投石车"守军 vs 第三波推进"的位置分区阈值(格)：
// 距敌方大本营(攻城武器厂)超过此距离 → 视为已出动推进的第三波投石车，允许祭司转化；
// 否则视为守家投石车，不转化（符合"只转化第三波刷出的投石车"要求）。
static const int THROWER_WAVE3_MIN_DIST_FROM_SIEGE = 25;
// 未探明敌方大本营时的兜底阈值(格)：投石车距我方市镇中心在此距离内 → 视为推进来的第三波投石车
static const int THROWER_WAVE3_MAX_DIST_FROM_CENTER = 45;
// 第三波决策三条规则的判定函数（定义在下方，此处前置声明以便 controlPriest 等提前使用）
static bool isWave3RushBronze(const tagInfo& info);
static bool isInTowerRange(const tagInfo& info, double dr, double ur);
static bool isWave3StoneThrower(const tagInfo& info, const tagArmy& thrower);
// ==================== 建筑选址记录（tryBuild 成功后记录，防失败漂移） ====================
static int g_lastBuildDR = -1, g_lastBuildUR = -1, g_lastBuildSize = -1;
static std::set<std::pair<int,int>> g_frameBuildPos;   // 本帧已选建造位（防同帧两个建筑选同一位置重叠）
static int g_buildSeq = 0;                             // 建筑序号（outward 选址角度旋转，不同建筑落在不同方向）
// ==================== 农民卡住检测（240 帧无变化 → 挪动换活） ====================
static std::map<int, int>    g_stuckFrame;    // SN -> 连续卡住帧数
static std::map<int, double> g_stuckDR, g_stuckUR;   // 上次位置
static std::map<int, int>    g_stuckState, g_stuckRes; // 上次状态/手持资源
static std::map<int, int>    g_stuckCooldown;// SN -> 下次可检测帧号
// ==================== 箭塔研发状态机 ====================
// 阶段：0=未研发 1=已下指令待开始 2=谷仓研发中 3=研发完成（可建塔）
static int g_towerPhase = 0;
static int g_towerWaitFrame = 0;   // 下指令帧号（5 秒未开始视为失败重试）
static int g_towerStartFrame = 0;  // 研发实际开始帧号（防"研发被打断"误判成完成）
// ==================== 祭司移动命令粘滞 ====================
// Core 中 HumanMove 会取消并重新建立当前路径；每帧重发相同命令会让单位无法真正走出第一步。
enum PriestMoveMode { PRIEST_MOVE_NONE = 0, PRIEST_MOVE_RETREAT, PRIEST_MOVE_FOLLOW, PRIEST_MOVE_OBJECTIVE };
static int    g_priestMoveMode = PRIEST_MOVE_NONE;
static double g_priestMoveDR = 0, g_priestMoveUR = 0;
static int    g_priestMoveFrame = -100000;
static int    g_priestRetreatUntil = -100000;   // 撤退迟滞：撤退后若干帧内不重新逼近转化目标（修祭司慢速振荡）
static double g_priestRetreatTX = -1, g_priestRetreatTY = -1;  // 撤守目标（粘性）：锁定后 150 帧不再重算，消除每帧横跳
static int    g_priestRetreatCommit = -100000;
// 祭司当前锁定的转化目标 SN。军队需避让此目标（不主动攻击），否则会在祭司读条完成前
// 先把投石车打死，导致"取消严禁攻击"后祭司反而永远转化不到。由 controlPriest 维护，
// controlMilitary 读取（注意 processData 中 controlMilitary 先于 controlPriest 执行，
// 故军队读到的是上一帧的锁定目标——目标通常持续多帧，够用）。
static int    g_priestConvertTargetSN = -1;
// ==================== 反攻状态机 ====================
// 阶段：NONE 防守期 → SCOUT 侦察探路 → CLEAR 贴边清场 → CONVERT 祭司进场转化
enum OffensePhase { OFFENSE_NONE = 0, OFFENSE_SCOUT, OFFENSE_CLEAR, OFFENSE_CONVERT };
static int g_offensePhase = OFFENSE_NONE;
static double g_siegeKnownDR = 0, g_siegeKnownUR = 0;  // 已探明的敌方攻城厂真实坐标
static bool   g_siegeKnown = false;                     // 是否已探到攻城厂
static int    g_scoutSN = -1;                           // 侦察骑兵 SN
static int    g_scoutTrainFrame = -1;                   // 侦察兵训出时刻帧（scoutFoodReserve 熔断用，-1=未训出）
static int    g_scoutLastOrderFrame = -100000;          // 侦察兵上次下令帧（防重复下令抖路）
// 侦察兵探路锚点索引（0..3 循环）：0=镜像点(对角) 1=水平镜像 2=垂直镜像 3=市中心。
// 旧语义是"L形路点状态机"（硬编码 22,20 / 78,16 / 78,86），只适配 map.njust，
// 随机到 map1/map2 会撞斜向海带卡死，故改为按市中心动态推导锚点，不依赖具体地图坐标。
static int    g_scoutPhase = 0;
// 方案F2：无进展超时换相。以"前进锚点块"为基准，侦察兵块位置曼哈顿距离>=3 即刷新；
// 长时间净位移<3格说明在极小区域打转（摆动/死胡同/海锚点），强制 phase++ 脱困。
static int    g_scoutNoProgressFrame = 0;
static int    g_scoutNoProgressBX = -1;
static int    g_scoutNoProgressBY = -1;
static std::vector<std::pair<int,int>> g_scoutPath;     // 侦察兵实际走过的块坐标序列（供士兵复用）
static std::map<int,int> g_armyLastOrderFrame;          // 士兵 SN -> 上次移动下令帧（防死循环重发）
static std::map<int,std::pair<int,int>> g_towerCmd;     // 箭塔 SN -> (目标SN, 下令帧)（防抖：同目标45帧内不重发，避免打断攻击）
// ==================== 临时统计日志状态（分析用，非策略；分析完成后可整段删除） ====================
static int  s_statLastStage = -1;       // 上一帧时代（检测升铜器完成）
static bool s_statLastStable = false;   // 上一帧是否已有马厩（检测马厩建成）
static bool s_statLastScout = false;    // 上一帧是否有侦察兵（检测侦察兵训练完成）
static bool s_statLastSiege = false;    // 上一帧是否已探到攻城厂（检测探路成功）
static bool s_statLastOffense = false;  // 上一帧是否已进入总攻（检测总攻开始）
static bool s_statWave3Logged = false;  // 是否已记录第三波到来时的祭司存活
static int  s_statLastPriestSN = -2;    // 上一帧祭司 SN（检测祭司死亡）
// 远程兵种判定：投石兵/弓箭手/改良弓/复合弓/战车弓/投石车（贴边清场主力）
static bool isRangedUnit(int sort)
{
    return sort == AT_SLINGER || sort == AT_BOWMAN || sort == AT_IMPROVED
        || sort == AT_COMPOSITE_BOWMAN || sort == AT_CHARIOT_ARCHER
        || sort == AT_STONE_THROWER;
}
// 敌方建筑 SN 是否为攻城武器厂（只能由祭司转化取胜，士兵不得攻击打掉）
static bool isSiegeBuildingSN(const tagInfo& info, int sn)
{
    for (const auto& b : info.enemy_buildings)
        if (b.SN == sn && b.Type == BUILDING_SIEGE && b.Blood > 0) return true;
    return false;
}
// 判断块 (bdr,bur) 是否陆地可行走：非海洋、非未探索、非建筑占位。
// 浅滩(MAPPATTERN_SHOAL)可行走，故仅排除 OCEAN 与 UNKNOWN。
static bool isWalkable(const tagInfo& info, int bdr, int bur)
{
    if (bdr < 0 || bur < 0 || bdr >= MAP_L || bur >= MAP_U) return false;
    if (info.theMap != nullptr) {
        int tp = (*info.theMap)[bdr][bur].type;
        if (tp == MAPPATTERN_OCEAN || tp == MAPPATTERN_UNKNOWN) return false;
    }
    for (const auto& b : info.buildings) {
        int bs = (b.Type == BUILDING_HOME || b.Type == BUILDING_ARROWTOWER) ? 2 : 3;
        if (bdr >= b.BlockDR && bdr < b.BlockDR + bs && bur >= b.BlockUR && bur < b.BlockUR + bs)
            return false;
    }
    return true;
}
// 块 (bdr,bur) 周围 margin 格内是否无障碍（海/树/建筑）——用于选"与障碍物保持间隔"的行走目标
static bool obstacleClear(const tagInfo& info, int bdr, int bur, int margin)
{
    for (int i = bdr - margin; i <= bdr + margin; i++) {
        for (int j = bur - margin; j <= bur + margin; j++) {
            if (i < 0 || j < 0 || i >= MAP_L || j >= MAP_U) continue;
            if (info.theMap != nullptr && (*info.theMap)[i][j].type == MAPPATTERN_OCEAN) return false;
        }
    }
    const double BLOCK = double(BLOCKSIDELENGTH);
    for (const auto& r : info.resources) {
        if (r.Type != RESOURCE_TREE || r.Cnt <= 0) continue;
        int tb = (int)(r.DR / BLOCK), tu = (int)(r.UR / BLOCK);
        if (abs(tb - bdr) <= margin && abs(tu - bur) <= margin) return false;
    }
    for (const auto& b : info.buildings) {
        int bs = (b.Type == BUILDING_HOME || b.Type == BUILDING_ARROWTOWER) ? 2 : 3;
        if (bdr - margin < b.BlockDR + bs && b.BlockDR < bdr + 1 + margin &&
            bur - margin < b.BlockUR + bs && b.BlockUR < bur + 1 + margin) return false;
    }
    return true;
}
// ==================== 兵种判定 ====================
// 转化价值（祭司滚雪球优先吃高价值）
static int armyValueScore(int sort)
{
    switch (sort) {
    case AT_STONE_THROWER:  return 100;
    case AT_CAVALRY:        return 80;
    case AT_HOPLITE:        return 70;
    case AT_BROADSWORDSMAN: return 70;
    case AT_COMPOSITE_BOWMAN: return 60;
    case AT_CHARIOT_ARCHER: return 55;
    case AT_CHARIOT:        return 50;
    case AT_IMPROVED:       return 45;
    case AT_BOWMAN:         return 40;
    case AT_SLINGER:        return 35;
    case AT_SCOUT:          return 35;
    default:                return 30;   // 棍棒等
    }
}
// 我方军队重心（排除祭司）
static bool armyCenterPos(const tagInfo& info, double& dr, double& ur)
{
    double sx = 0, sy = 0; int n = 0;
    for (const auto& a : info.armies) {
        if (a.Sort == AT_PRIEST) continue;
        sx += a.DR; sy += a.UR; n++;
    }
    if (n == 0) return false;
    dr = sx / n; ur = sy / n;
    return true;
}
void UsrAI::processData()
{
    tagInfo info = getInfo();
    g_frameBuildPos.clear();     // 每帧清空本帧建造位互斥集合
    // 游戏重开检测（GameFrame 回退）：重置全部跨帧状态，防止旧局残留污染新局
    static int g_lastGameFrame = -1;
    if (info.GameFrame < g_lastGameFrame) {
        g_towerPhase = 0;
        g_towerWaitFrame = 0;
        g_towerStartFrame = 0;
        towerResearched = false;
        g_stuckFrame.clear();  g_stuckDR.clear();  g_stuckUR.clear();
        g_stuckState.clear();  g_stuckRes.clear(); g_stuckCooldown.clear();
        g_lastBuildDR = -1; g_lastBuildUR = -1; g_lastBuildSize = -1;
        g_jobRound = 0;
        g_farmerTargetSN.clear();
        g_buildDispatch.clear();
        g_swordResearched = false;
        g_meleeResearched = false;
        g_towerUpgradeResearched = false;
        g_logisticsResearched = false;
        g_wheelResearched = false;
        g_compositeResearched = false;
        g_woodUpgradeResearched = false;
        g_watchComposite = TechWatch();
        g_watchWheel = TechWatch();
        g_watchLogistics = TechWatch();
        g_underAttack = false;
        g_farmerFarm.clear();
        g_ownedFarms.clear();
        g_priestMoveMode = PRIEST_MOVE_NONE;
        g_priestMoveFrame = -100000;
        g_offensePhase = OFFENSE_NONE;
        g_siegeKnownDR = 0; g_siegeKnownUR = 0; g_siegeKnown = false;
        g_scoutSN = -1;
        g_scoutTrainFrame = -1;
        g_scoutLastOrderFrame = -100000;
        g_scoutPhase = 0;
        g_scoutNoProgressFrame = 0;
        g_scoutNoProgressBX = -1;
        g_scoutNoProgressBY = -1;
        g_scoutPath.clear();
        g_armyLastOrderFrame.clear();
        g_towerCmd.clear();
        g_buildSeq = 0;
        s_statLastStage = -1;
        s_statLastStable = false;
        s_statLastScout = false;
        s_statLastSiege = false;
        s_statLastOffense = false;
        s_statWave3Logged = false;
        s_statLastPriestSN = -2;
    }
    g_lastGameFrame = info.GameFrame;
    g_assigned.clear();          // 每帧重置防冲突集合
    g_buildAssigned.clear();     // 每帧重置建造防冲突集合
    g_farmAssigned.clear();      // 每帧重置农田占用集合
    pruneFarmLeases(info);       // 先回收失效锁定（死农民/采空田），再派工
    controlBuilding(info);       // 建筑优先：先派农民建造（若 economy 先派工占满 IDLE 农民，tryBuild 抢不到人）
    controlFarmerDefense(info);  // 村民反击：敌军来袭检测 + 反击调度（先于 economy，反击村民不被派去采集）
    controlEconomy(info);        // 经济：造村民 + 剩余空闲村民派工
    controlMilitary(info);       // 军事：训练 + 防守 + 反攻
    controlTowers(info);         // 箭塔指挥：User 层索敌下令（引擎自动索敌失效，需手动点名）
    controlPriest(info);         // 祭司：转化 / 治疗 / 回退
    detectStuck(info);           // 农民卡住兜底

    // ============ 临时统计日志（分析用，非策略；分析完成后可整段删除） ============
    {
        if (s_statLastStage == -1)
            qInfo() << "[STAT] session_start frame" << info.GameFrame;
        static int s_heartbeat = -1;
        if (info.GameFrame / 3000 != s_heartbeat) {
            s_heartbeat = info.GameFrame / 3000;
            qInfo() << "[STAT] heartbeat frame" << info.GameFrame;
        }
        int stage = info.civilizationStage;
        bool hasStable = countBuildingBuilt(info, BUILDING_STABLE) >= 1;
        bool hasScout = false;
        for (const auto& a : info.armies) if (a.Sort == AT_SCOUT) { hasScout = true; break; }
        bool offense = (info.GameFrame > 21000 && countArmy(info) >= 12) || info.GameFrame > 26000;

        if (s_statLastStage == CIVILIZATION_TOOLAGE && stage == CIVILIZATION_BRONZEAGE)
            qInfo() << "[STAT] bronze_done frame" << info.GameFrame;
        if (!s_statLastStable && hasStable)
            qInfo() << "[STAT] stable_built frame" << info.GameFrame;
        if (!s_statLastScout && hasScout)
            qInfo() << "[STAT] scout_trained frame" << info.GameFrame;
        if (!s_statLastSiege && g_siegeKnown) {
            int sdr = -1, sur = -1;
            for (const auto& b : info.enemy_buildings)
                if (b.Type == BUILDING_SIEGE) { sdr = b.BlockDR; sur = b.BlockUR; break; }
            qInfo() << "[STAT] siege_found frame" << info.GameFrame
                    << "siege_dr" << sdr << "siege_ur" << sur;
        }
        if (!s_statLastOffense && offense) {
            int ea = 0, eb = 0;
            for (const auto& a : info.enemy_armies) if (a.Blood > 0) ea++;
            for (const auto& b : info.enemy_buildings) if (b.Blood > 0) eb++;
            qInfo() << "[STAT] offense_start frame" << info.GameFrame
                    << "enemy_army" << ea << "enemy_build" << eb
                    << "my_meat" << info.Meat << "my_wood" << info.Wood
                    << "my_stone" << info.Stone << "my_gold" << info.Gold
                    << "my_army" << countArmy(info) << "my_farmer" << countFarmers(info);
        }
        if (!s_statWave3Logged && info.GameFrame >= 21000) {
            int p = findPriestSN(info);
            qInfo() << "[STAT] wave3_arrive frame" << info.GameFrame << "priest_alive" << (p >= 0 ? 1 : 0);
            s_statWave3Logged = true;
        }
        int priestNow = findPriestSN(info);
        if (s_statLastPriestSN >= 0 && priestNow < 0)
            qInfo() << "[STAT] priest_died frame" << info.GameFrame;

        s_statLastStage = stage;
        s_statLastStable = hasStable;
        s_statLastScout = hasScout;
        s_statLastSiege = g_siegeKnown;
        s_statLastOffense = offense;
        s_statLastPriestSN = priestNow;
    }
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
        if (a.Blood <= 0) continue;
        double d = calDistance(pr, pu, a.DR, a.UR);
        if (d < bd) { bd = d; best = a.SN; }
    }
    for (const auto& f : info.enemy_farmers) {
        if (f.Blood <= 0) continue;
        double d = calDistance(pr, pu, f.DR, f.UR);
        if (d < bd) { bd = d; best = f.SN; }
    }
    for (const auto& b : info.enemy_buildings) {
        if (b.Blood <= 0) continue;
        double d = calDistance(pr, pu, (b.BlockDR + 0.5) * BLOCK, (b.BlockUR + 0.5) * BLOCK);
        if (d < bd) { bd = d; best = b.SN; }
    }
    outDist = bd;
    return best;
}
// 正在攻击祭司的敌人 SN（WorkObjectSN 指向祭司）
int UsrAI::findAttackerSN(const tagInfo& info, int priestSN)
{
    for (const auto& a : info.enemy_armies)  if (a.Blood > 0 && a.WorkObjectSN == priestSN) return a.SN;
    for (const auto& f : info.enemy_farmers) if (f.Blood > 0 && f.WorkObjectSN == priestSN) return f.SN;
    return -1;
}
// 血量百分比最低的残血友军 SN（含祭司本人——内核支持祭司自疗，与 UI 手动右键自己一致）
int UsrAI::findWoundedAllySN(const tagInfo& info, int priestSN)
{
    (void)priestSN;   // 保留参数兼容调用；祭司自己也是治疗候选，不再排除
    int best = -1; double br = 1e18;
    auto consider = [&](int sn, int blood, int maxblood) {
        if (maxblood <= 0 || blood >= maxblood) return;
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
// ==================== 祭司状态机 ====================
void UsrAI::controlPriest(const tagInfo& info)
{
    const double BLOCK = double(BLOCKSIDELENGTH);
    const double CONVERT_RANGE = double(DIS_PRIEST) * BLOCK;

    int priestSN = findPriestSN(info);
    if (priestSN < 0) { g_priestConvertTargetSN = -1; return; }   // 祭司阵亡 → 军队解除避让
    const tagArmy* priest = nullptr;
    for (const auto& a : info.armies) if (a.SN == priestSN) { priest = &a; break; }
    if (!priest) { g_priestConvertTargetSN = -1; return; }

    // 维护"祭司锁定目标"（军队避让用）：目标已死亡则清空，避免军队无意义地长期避让死人
    if (g_priestConvertTargetSN >= 0) {
        bool targetAlive = false;
        for (const auto& a : info.enemy_armies)
            if (a.SN == g_priestConvertTargetSN && a.Blood > 0) { targetAlive = true; break; }
        if (!targetAlive) g_priestConvertTargetSN = -1;
    }

    // 反攻阶段判定（与 controlMilitary 一致：攒够 12 兵就总攻，后期加快推进；26000 帧兜底）
    bool offense = (info.GameFrame > 21000 && countArmy(info) >= 12)
                || info.GameFrame > 26000;

    // HumanMove 是可覆盖的命令。正在走路时若每帧重复下发，会重置寻路进度，表现为原地不动。
    // 相同移动意图只发一次；目标/模式真正切换，或上一次移动已结束失败时才重新发命令。
    auto issueMove = [&](int mode, double dr, double ur, double stopDistance) -> bool {
        // 保存"上一次下发的模式"：下方迟滞判定要据此区分「新触发撤退」与「防抖重发同一撤退」。
        // 必须在 g_priestMoveMode 被覆盖(下方)之前取，否则读到的就是本次 mode，永远判不出新撤退。
        const int prevMode = g_priestMoveMode;
        if (calDistance(priest->DR, priest->UR, dr, ur) <= stopDistance) return false;
        // 防抖（修振荡根因）：原逻辑只在"同模式(sameMode)"下防抖，但祭司逼近/撤退每帧在
        // FOLLOW↔RETREAT 间翻转 → sameMode 恒假 → 每帧重发 HumanMove 重置寻路 → 表现原地/来回走。
        // 改为：正在走路时，只要目标点相对上次指令变化 <2 格就保留当前路径（与模式无关）；
        // 目标点变化较大时也至少间隔 45 帧再重发，杜绝每帧翻转。
        if (priest->NowState == HUMAN_STATE_WALKING) {
            if (calDistance(g_priestMoveDR, g_priestMoveUR, dr, ur) <= 2 * BLOCK) return false;
            if (info.GameFrame - g_priestMoveFrame < 45) return false;
        }
        HumanMove(priestSN, dr, ur);
        // [日志探针] 每次真正下发的祭司移动指令 → 事后可检测"来回走/振荡"(方向反复反转)
        qInfo() << "[STAT] priest_move frame" << info.GameFrame << "mode" << mode
                << "dr" << int(dr / BLOCK) << "ur" << int(ur / BLOCK);
        g_priestMoveMode = mode;
        g_priestMoveDR = dr;
        g_priestMoveUR = ur;
        g_priestMoveFrame = info.GameFrame;
        // 撤退迟滞（2026-08-31 修：防无限续期死锁）
        // 原逻辑：每下发一次 RETREAT 就把迟滞推后 90 帧。但本函数防抖重发间隔仅 45 帧(见上)，
        // 45 < 90 → 每重发一次，迟滞终点再往后推 90 → 迟滞无限续期 → 下方 FOLLOW 门控
        // (info.GameFrame >= g_priestRetreatUntil) 恒为假 → 祭司永远无法主动逼近转化目标，
        // 只能被动等敌人自己走进 12 格 → 转化率暴跌(map1 run5 实测 5/68)→ 军力断供崩盘(死 16935)。
        // 改法：仅「新触发撤退」时设迟滞；同一撤退的防抖重发不续期，让迟滞能自然到期。
        if (mode == PRIEST_MOVE_RETREAT) {
            const bool newRetreat = (prevMode != PRIEST_MOVE_RETREAT)
                                 || (info.GameFrame >= g_priestRetreatUntil);
            if (newRetreat) g_priestRetreatUntil = info.GameFrame + 90;
        }
        return true;
    };
    auto retreatToSafe = [&]() -> bool {
        // 灵活撤退（随机应变，避免伤害第一）：
        // 被敌人追击时，在「军队重心(人密集处)」和「远离最近敌人方向」两个候选中，
        // 选离最近敌人更远、更安全的那一个——军队方向安全才去，被敌人挡路就远离敌人，不硬冲。
        // 找最近的已建成箭塔（祭司安全屋：箭塔护体 + 开火拉仇恨，追兵必撞进塔射程）
        double tdr = 0, tur = 0;
        bool hasTower = false;
        {
            double bt = 1e18;
            for (const auto& b : info.buildings) {
                if (b.Type != BUILDING_ARROWTOWER || b.Percent < 100) continue;
                double bdr = (b.BlockDR + 0.5) * BLOCK, bur = (b.BlockUR + 0.5) * BLOCK;
                double d = calDistance(priest->DR, priest->UR, bdr, bur);
                if (d < bt) { bt = d; tdr = bdr; tur = bur; hasTower = true; }
            }
        }
        double nd = 1e18;
        int ne = nearestEnemyUnitSN(info, priest->DR, priest->UR, nd);
        if (ne >= 0) {
            // 敌人 18 格内就提前撤离（在敌人打过来之前撤，而非贴脸才跑，避免被打死）
            if (nd > 18 * BLOCK) return false;   // 敌人尚远，暂时安全
            /* 旧做法：敌人来了就贴到箭塔旁 2 格。问题是贴塔=固定靶——
               近战兵/远程兵速度 2.439 快于祭司 2.033，围上来只能站着挨打。
            if (hasTower) return issueMove(PRIEST_MOVE_RETREAT, tdr, tur, 2 * BLOCK);
            */
            // 新做法：绕到**塔的背面**（让塔挡在祭司与敌人之间），而非躲到塔下。
            // 绕塔能甩开追兵的三重原因：
            //   ① 塔是 2x2 实体建筑，近战兵追击必须绕行，路径被拉长；
            //   ② 祭司绕小圈、追兵绕大圈：追兵所需线速度 = v_priest*(R+d)/R
            //      （R=3.5 绕行半径、d=2 落后距离 → 2.033*5.5/3.5≈3.19）> 追兵实际 2.439 → 追不上；
            //   ③ 塔持续开火拉仇恨，祭司距塔仅 3.5 格（远小于 7 格射程），保护一点不减。
            if (hasTower) {
                double ex = 0, ey = 0;
                if (ne >= 0 && enemyDetailPos(info, ne, ex, ey)) {
                    double vx = tdr - ex, vy = tur - ey;      // 由敌人指向塔的方向
                    double vl = std::sqrt(vx * vx + vy * vy);
                    if (vl > 0.01) {
                        const double R = 3.5 * BLOCK;          // 绕行半径：贴塔借掩体，仍在 7 格射程内
                        const double base = std::atan2(vy, vx);
                        const double OFF[5] = { 0.0, 0.6, -0.6, 1.2, -1.2 };  // 正背面优先，再两侧微调
                        for (double off : OFF) {
                            double ang = base + off;
                            double ox = tdr + std::cos(ang) * R;
                            double oy = tur + std::sin(ang) * R;
                            int bi = int(ox / BLOCK), bj = int(oy / BLOCK);
                            if (bi < 0 || bj < 0 || bi >= MAP_L || bj >= MAP_U) continue;
                            if (!isWalkable(info, bi, bj)) continue;
                            return issueMove(PRIEST_MOVE_RETREAT, ox, oy, BLOCK);
                        }
                    }
                }
                // 拿不到敌人方位 / 背面一圈都不可走 → 退回塔旁
                return issueMove(PRIEST_MOVE_RETREAT, tdr, tur, 2 * BLOCK);
            }
            double ed = 0, eu = 0;
            bool hasEnemy = enemyDetailPos(info, ne, ed, eu);

            // 候选1：军队重心（人密集处，士兵会转火保护）
            double adr = 0, aur = 0;
            bool hasArmy = armyCenterPos(info, adr, aur);

            // 候选2：远离最近敌人的方向点
            double fx = 0, fy = 0;
            bool hasFlee = false;
            if (hasEnemy) {
                double dx = priest->DR - ed, dy = priest->UR - eu;
                double dl = std::sqrt(dx * dx + dy * dy);
                if (dl < 1) { dx = 1; dy = 0; dl = 1; }
                fx = priest->DR + dx / dl * 15 * BLOCK;
                fy = priest->UR + dy / dl * 15 * BLOCK;
                if (fx < BLOCK) fx = BLOCK;
                if (fy < BLOCK) fy = BLOCK;
                if (fx > (MAP_L - 1) * BLOCK) fx = (MAP_L - 1) * BLOCK;
                if (fy > (MAP_U - 1) * BLOCK) fy = (MAP_U - 1) * BLOCK;
                hasFlee = true;
            }

            // 后方锚点：最近箭塔（无塔则市中心）。总攻期军队前压时，"撤向军队"=留在危险区，
            // 必须改撤向"后方"（塔/家），祭司才真正脱离战场。见 map2 祭司 dr61-67/ur78-83 抖动被围杀。
            double rx = 0, ry = 0; bool hasRear = false;
            if (hasTower) { rx = tdr; ry = tur; hasRear = true; }
            else { int bdr = 0, bur = 0; if (centerBlockPos(info, bdr, bur)) { rx = (bdr + 0.5) * BLOCK; ry = (bur + 0.5) * BLOCK; hasRear = true; } }

            // 撤守目标"粘性"：决定撤离后锁定同一目标 150 帧，避免每帧在军队/远离点间反复横跳（实测抖动被围杀）。
            if (info.GameFrame > g_priestRetreatCommit || g_priestRetreatTX < 0) {
                double tx = -1, ty = -1;
                // 军队若比祭司更靠近敌人，说明军队已前压，撤向军队只会留在危险区 → 优先撤向后方锚点
                bool armyForward = hasArmy && calDistance(adr, aur, ed, eu) < calDistance(priest->DR, priest->UR, ed, eu);
                if (hasRear && !armyForward)      { tx = rx;  ty = ry; }
                else if (hasFlee)                 { tx = fx;  ty = fy; }
                else if (hasRear)                 { tx = rx;  ty = ry; }
                else if (hasArmy)                 { tx = adr; ty = aur; }
                if (tx >= 0) { g_priestRetreatTX = tx; g_priestRetreatTY = ty; g_priestRetreatCommit = info.GameFrame + 150; }
            }
            if (g_priestRetreatTX >= 0)
                return issueMove(PRIEST_MOVE_RETREAT, g_priestRetreatTX, g_priestRetreatTY, 2 * BLOCK);
            // 兜底：无任一候选
            if (hasArmy) return issueMove(PRIEST_MOVE_RETREAT, adr, aur, 3 * BLOCK);
            if (hasFlee) return issueMove(PRIEST_MOVE_RETREAT, fx, fy, 2 * BLOCK);
        }
        // 无敌人：有箭塔则回箭塔旁待命（留家=回塔，最安全）；无塔才靠拢军队/回市中心
        if (hasTower)
            return issueMove(PRIEST_MOVE_RETREAT, tdr, tur, 2 * BLOCK);
        double adr = 0, aur = 0;
        if (armyCenterPos(info, adr, aur))
            return issueMove(PRIEST_MOVE_FOLLOW, adr, aur, 3 * BLOCK);
        int bdr = 0, bur = 0;
        if (!centerBlockPos(info, bdr, bur)) return false;
        return issueMove(PRIEST_MOVE_RETREAT, (bdr + 0.5) * BLOCK, (bur + 0.5) * BLOCK, 2 * BLOCK);
    };

    // 方案Y（2026-08-31）：hasEnemyUnit 拆成两个量。
    // hasCombatUnit：只认战斗单位(enemy_armies)，作为巡逻门控 —— 否则敌方农民常驻导致
    // hasEnemyUnit 永远为真，912 行巡逻分支几乎不可达 → 祭司平时一动不动、探视野丢失。
    // hasEnemyUnit：战斗单位+农民，保留供撤退保护等场景使用（下方 655 行已改走 hasCombatUnit）。
    bool hasEnemyUnit = false;
    bool hasCombatUnit = false;
    for (const auto& a : info.enemy_armies) if (a.Blood > 0) { hasEnemyUnit = true; hasCombatUnit = true; break; }
    if (!hasEnemyUnit)
        for (const auto& f : info.enemy_farmers) if (f.Blood > 0) { hasEnemyUnit = true; break; }

    // 箭塔威胁检测：敌方箭塔在祭司7格内（箭塔射程）即视为能打到祭司
    bool towerThreat = false;
    for (const auto& b : info.enemy_buildings) {
        if (b.Type == BUILDING_ARROWTOWER && b.Blood > 0) {
            double bdr = (b.BlockDR + 0.5) * BLOCK, bur = (b.BlockUR + 0.5) * BLOCK;
            if (calDistance(priest->DR, priest->UR, bdr, bur) <= 7 * BLOCK) {
                towerThreat = true; break;
            }
        }
    }

    // 诊断探针：祭司周围敌人构成（定位死亡原因，600帧去重 + 低血事件）
    {
        static int s_lastDiag = -100000;
        bool lowBlood = priest->Blood < 70;
        if (info.GameFrame - s_lastDiag >= 300 || lowBlood) {
            double d1 = 1e18, d2 = 1e18, d3 = 1e18; int s1 = -1, s2 = -1, s3 = -1;
            int cnt = 0;
            for (const auto& e : info.enemy_armies) {
                if (e.Blood <= 0) continue;
                cnt++;
                double d = calDistance(priest->DR, priest->UR, e.DR, e.UR);
                if (d < d1)      { d3 = d2; s3 = s2; d2 = d1; s2 = s1; d1 = d; s1 = e.Sort; }
                else if (d < d2) { d3 = d2; s3 = s2; d2 = d; s2 = e.Sort; }
                else if (d < d3) { d3 = d; s3 = e.Sort; }
            }
            int tl = findAttackerSN(info, priestSN); int tlSort = -1;
            if (tl >= 0) for (const auto& e : info.enemy_armies) if (e.SN == tl) { tlSort = e.Sort; break; }
            // 方位挡刀统计（纯探针，不改逻辑）：最近战斗单位敌（排除农民）的方位上，
            // army 在"祭司→敌"方向前方（投影 > 2 格）且横向偏离 < 4 格的个数。
            // 用于验证"方位掩护判定"是否值得做：若死亡前 frontCover 常为 0，说明祭司确实在裸奔。
            int frontCover = 0; double ndA = 1e18; double exA = 0, eyA = 0;
            for (const auto& e : info.enemy_armies) {
                if (e.Blood <= 0) continue;
                double d = calDistance(priest->DR, priest->UR, e.DR, e.UR);
                if (d < ndA) { ndA = d; exA = e.DR; eyA = e.UR; }
            }
            if (ndA < 1e17) {
                double px = exA - priest->DR, py = eyA - priest->UR;
                double pl = std::sqrt(px * px + py * py);
                if (pl > 1) {
                    for (const auto& a : info.armies) {
                        if (a.Sort == AT_PRIEST || a.Blood <= 0) continue;
                        double ax = a.DR - priest->DR, ay = a.UR - priest->UR;
                        double proj = (ax * px + ay * py) / pl;
                        double perp = std::abs(ax * py - ay * px) / pl;
                        if (proj > 2 * BLOCK && perp < 4 * BLOCK) frontCover++;
                    }
                }
            }
            qInfo() << "[STAT] priest_diag frame" << info.GameFrame
                    << "blood" << int(priest->Blood)
                    << "nearcnt" << cnt
                    << "s1" << s1 << "d1" << int(d1 / BLOCK)
                    << "s2" << s2 << "d2" << int(d2 / BLOCK)
                    << "s3" << s3 << "d3" << int(d3 / BLOCK)
                    << "throwerLock" << tlSort
                    << "frontCover" << frontCover
                    << "ndA" << (ndA > 1e17 ? -1 : int(ndA / BLOCK));
            s_lastDiag = info.GameFrame;
        }
    }

    // 低血量的撤退可打断任何动作；冷却中的转化动作会在挥手完成后自然回到空闲。
    // 防守 40 / 反攻 60：祭司 100 血 0 防，投石车单发 50。反攻阈值原 50 在"100→50→0"之间
    // 无撤退窗口（挨一发后血=50，50<50 为假→不撤→必死于第二发）；提到 60 后挨一发(血50)即撤，
    // 获得撤退窗口。防守阈值维持 40（防守期敌人伤害较低，风险可控；如需更保守可提到 50）。
    const int bloodThreshold = offense ? 60 : 40;
    if (priest->Blood < bloodThreshold) { retreatToSafe(); return; }

    // 投石车（50攻/10射程）锁定祭司 → 立即撤，不等掉血。投石车两发 50 直接秒杀，
    // 血阈值 40 在"100→50→0"之间没有撤退窗口，故用"被投石车瞄准"这个信号提前拦截。
    // 放在"施法不打扰"之前：即使正在读条被投石车锁定也打断撤退（保命优先于转化）。
    {
        int throwerAttacker = findAttackerSN(info, priestSN);
        if (throwerAttacker >= 0) {
            for (const auto& e : info.enemy_armies)
                if (e.SN == throwerAttacker && e.Sort == AT_STONE_THROWER) { retreatToSafe(); return; }
        }
    }

    // 【近战 standoff 已撤销 —— 实测 0/7 全灭，明确负优化，勿再试】
    // 原方案：最近近战敌 <12 格(无 army 掩护) 或 <8 格(硬撤) 就 retreatToSafe()，置于转化逻辑之前。
    // 实测(m1D×4 / m2D×3, 2026-08-31)：**7 局祭司全部阵亡**，死亡帧 14901~18075；
    // 对比撤销前 map2 3/3、map1 2/3。典型序列：~7000 帧首次撤退 ndM=11 → 600 帧后 ndM=4~5 → 死。
    // 失败根因（两条叠加）：
    //  ① 物理上甩不掉：近战(棍棒/骑/方阵/阔剑)速度 2.439 > 祭司 2.033，越撤距离越近（实测 11→4），
    //     "保持距离"在本引擎数值下不成立——这是速度差决定的，不是参数没调好。
    //  ② 转化被禁：祭司转化站位固定在 11 格，而 11 < 12 触发 standoff → 等于永久禁止转化近战兵。
    //     实测 convertStart 掉到 0~5 次（正常应显著更高），祭司只逃不产出，纯亏。
    // 结论：对**可转化**目标，站定读条(2~6s, 成功即敌人变友军)远安全于逃跑。
    // 若仍需防近战，正确方向是"掩护判定"(有 army 更近接敌才转化，改动15 安全线已在做)，
    // 而非距离 standoff。

    // 已经开始转换时绝不重发指令。重新下令会打断 2~6 秒的转换读条。
    /* 曾尝试"近战兵 6 格内打断读条撤退"，实测是明显负优化（三局祭司全阵亡，
       map 甚至在 8026 帧第三波之前就死）。原因：站定读完条 = 转化成功 = 敌人变友军（安全）；
       而打断后转化失败、敌人还在，祭司速度 2.033 又跑不过近战兵 2.439，只能被追着砍死。
       结论：对**能转化**的目标，站定读条反而比逃跑安全，故恢复为不打断。
    if (NowState == HUMAN_STATE_ATTACKING) { if (近战<=6格) retreatToSafe(); return; }
    */
    if (priest->NowState == HUMAN_STATE_ATTACKING) return;

    // 方案Y：战斗门控改用 hasCombatUnit（仅战斗单位）。只有农民(无战斗单位)时不再进入
    // 本战斗/转化分支，而是落入 912 行巡逻分支探视野 —— 修复"祭司平时一动不动"。
    if (hasCombatUnit) {
        if (priest->ConvertCooldown > 0) {
            // 冷却期：防守期拉开距离；反攻期保持距离即可、不来回撤退（转化射程远于敌方攻击，
            // 站定等冷却结束继续转化），仅被贴身攻击时拉开。
            if (offense) {
                int atk = findAttackerSN(info, priestSN);
                if (atk >= 0) retreatToSafe();
                return;
            }
            retreatToSafe();
            return;
        }

        // C+ 转化：价值优先（第三波投石车 1000 > armyValueScore），但**只挑安全可达的目标**——
        // 目标 6 格内敌人 >=3 说明深陷敌堆，去转化它就得走进敌堆送死 → 跳过；
        // 过远(>34格)的目标同样跳过（长途穿越 = 送死）。
        // 选中后祭司只逼近到自身转化射程边缘(11格)就停住持续转化，绝不继续靠近。
        // 注：旧的"垂直绕行"已删除（见下方），安全性改由本段目标选择把关。
        int target = -1;
        double tdr = 0, tur = 0;
        int attacker = findAttackerSN(info, priestSN);
        if (attacker >= 0 && enemyDetailPos(info, attacker, tdr, tur)) {
            target = attacker;   // 正在攻击祭司者优先（自救）
        } else {
            // 某点 6 格内的敌人数（判断候选目标是否深陷敌堆）
            auto guardCount = [&](double dr, double ur) -> int {
                int c = 0;
                for (const auto& e : info.enemy_armies)
                    if (e.Blood > 0 && calDistance(e.DR, e.UR, dr, ur) <= 6 * BLOCK) c++;
                return c;
            };
            const int GUARD_LIMIT = 3;             // 目标 6 格内敌人 >=3 → 视为深陷敌堆
            const double REACH_LIMIT = 34 * BLOCK; // 过远不去（避免长途穿越敌区）
            // 严格档：价值优先，且目标必须安全可达
            double bv = -1, bd = 1e18; int bestSN = -1;
            for (const auto& a : info.enemy_armies) {
                if (a.Blood <= 0) continue;
                double d = calDistance(priest->DR, priest->UR, a.DR, a.UR);
                if (d > REACH_LIMIT) continue;
                if (guardCount(a.DR, a.UR) >= GUARD_LIMIT) continue;
                // 第三波推进来的投石车价值 1000；守家投石车按普通价值处理（避免长途去敌基地）
                int v = (a.Sort == AT_STONE_THROWER && isWave3StoneThrower(info, a))
                        ? 1000 : armyValueScore(a.Sort);
                if (v > bv || (v == bv && d < bd)) { bv = v; bd = d; bestSN = a.SN; }
            }
            // 兜底档：都被敌堆包围或过远 → 退而求其次，只转化**最近**的敌人（绝不冒险深入）
            if (bestSN < 0) {
                bd = 1e18;
                for (const auto& a : info.enemy_armies) {
                    if (a.Blood <= 0) continue;
                    double d = calDistance(priest->DR, priest->UR, a.DR, a.UR);
                    if (d < bd) { bd = d; bestSN = a.SN; }
                }
                if (bestSN < 0)
                    for (const auto& f : info.enemy_farmers) {
                        if (f.Blood <= 0) continue;
                        double d = calDistance(priest->DR, priest->UR, f.DR, f.UR);
                        if (d < bd) { bd = d; bestSN = f.SN; }
                    }
            }
            // 目标粘性：选中后锁定 LOCK_FRAMES 帧，抑制"目标抖动"。
            // 实测（见 analyze_ai_log.py）：不加粘性时目标切换 74 次 → 祭司掉头 24 次/折返 20 次，
            // 每次换目标就改向 → 一直在路上、进不了转化射程（表现为"来回走 + 不转化"）。
            // 例外：若新目标是投石车(高价值)则允许立即改锁，不错过转化窗口。
            static int s_lockedSN = -1;
            static int s_lockFrame = -100000;
            const int LOCK_FRAMES = 250;
            auto stillAlive = [&](int sn) -> bool {
                if (sn < 0) return false;
                for (const auto& a : info.enemy_armies) if (a.SN == sn && a.Blood > 0) return true;
                for (const auto& f : info.enemy_farmers) if (f.SN == sn && f.Blood > 0) return true;
                return false;
            };
            bool bestIsThrower = false;
            for (const auto& a : info.enemy_armies)
                if (a.SN == bestSN && a.Sort == AT_STONE_THROWER) { bestIsThrower = true; break; }
            if (s_lockedSN >= 0 && s_lockedSN != bestSN
                && info.GameFrame - s_lockFrame < LOCK_FRAMES
                && stillAlive(s_lockedSN) && !bestIsThrower
                && enemyDetailPos(info, s_lockedSN, tdr, tur)) {
                bestSN = s_lockedSN;          // 沿用旧目标，抑制抖动
            } else {
                s_lockedSN = bestSN;          // 换新目标，重置锁定计时
                s_lockFrame = info.GameFrame;
            }
            if (bestSN >= 0) {
                target = bestSN;
                enemyDetailPos(info, bestSN, tdr, tur);
            }
        }

        if (target >= 0) {
            // 记录祭司锁定的转化目标 → 军队避让，不抢在祭司读条完成前把目标打死
            g_priestConvertTargetSN = target;
            // [日志探针] 祭司选中的转化目标（含兵种 Sort：可判断是否挑中投石车等高价值单位）
            {
                static int s_lastPickSN = -1;
                if (target != s_lastPickSN) {
                    s_lastPickSN = target;
                    int tsort = -1;
                    for (const auto& a : info.enemy_armies) if (a.SN == target) { tsort = a.Sort; break; }
                    qInfo() << "[STAT] convert_pick frame" << info.GameFrame
                            << "sn" << target << "sort" << tsort
                            << "d" << int(calDistance(priest->DR, priest->UR, tdr, tur) / BLOCK);
                }
            }
            double d = calDistance(priest->DR, priest->UR, tdr, tur);
            if (d <= CONVERT_RANGE) {
                // 射程内直接转化（只下发一次，避免不断重置转换读条）
                HumanAction(priestSN, target);
                g_priestMoveMode = PRIEST_MOVE_NONE;
                // 验证用：每次锁定"新的"转化对象时打一条日志，确认总攻期祭司确实在转化
                static int s_lastConvertLogged = -1;
                if (target != s_lastConvertLogged) {
                    s_lastConvertLogged = target;
                    // d = 本次转化时祭司到目标的距离（格）；12 为转化射程上限，d 越大越"擦边"
                    qInfo() << "[STAT] priest_convert_start frame" << info.GameFrame
                            << "target_sn" << target << "d" << int(d / BLOCK);
                }
                return;
            }
            // 射程外：朝目标单调逼近，停在自身转化射程边缘(11格)后持续转化，绝不继续靠近(不进敌堆)。
            // 旧"垂直绕行"已删除，原因：它是纯横向移动，到目标距离变为 √(d²+100)——**只增不减**，
            // 于是祭司永远进不了 12 格转化射程(表现为"不转化")，且绕行侧随最近威胁翻面而左右
            // 横跳(表现为"来回走")。安全性已改由上方目标选择(敌堆>=3 过滤 + 34 格距离上限)把关。
            // 11 格 = 祭司够得着转化(12格)、投石车够不着祭司(10格)的黄金区间。
            double dx = tdr - priest->DR, dy = tur - priest->UR;
            double dl = std::sqrt(dx * dx + dy * dy);
            if (dl < 1) { dx = 1; dy = 0; dl = 1; }
            double k = (d - 11 * BLOCK) / d;
            double gx = fmax(BLOCK, fmin(priest->DR + dx * k, (MAP_L - 1) * BLOCK));
            double gy = fmax(BLOCK, fmin(priest->UR + dy * k, (MAP_U - 1) * BLOCK));
            // 安全线（map1 已知死法：祭司被推前向钉死，成为最前单位被围杀）：
            // 若祭司是某近敌"最近的单位"（无 army 在更前/同线接敌掩护），则不清算逼近、改为撤退，
            // 强制祭司留在 army 火力掩护之后。缓冲 6 格允许祭司略前出于 army 前沿（转化射程 12 格需要）。
            {
                double ndP = 1e18; int neSN = nearestEnemyUnitSN(info, priest->DR, priest->UR, ndP);
                if (neSN >= 0 && ndP < 30 * BLOCK) {
                    double neX = 0, neY = 0;
                    if (enemyDetailPos(info, neSN, neX, neY)) {
                        bool covered = false;
                        for (const auto& a : info.armies) {
                            if (a.Sort != AT_PRIEST && a.Blood > 0
                                && calDistance(a.DR, a.UR, neX, neY) <= ndP + 6 * BLOCK) {
                                covered = true; break;
                            }
                        }
                        if (!covered) {
                            static int s_lastSafetyLog = -100000;
                            if (info.GameFrame - s_lastSafetyLog >= 600) {
                                s_lastSafetyLog = info.GameFrame;
                                qInfo() << "[STAT] priest_safety_retreat frame" << info.GameFrame
                                        << "ndP" << int(ndP / BLOCK);
                            }
                            retreatToSafe();
                            return;
                        }
                    }
                }
            }
            // 撤退迟滞期内不重新逼近（避免慢速振荡）；90 帧足够走出危险区
            if (info.GameFrame >= g_priestRetreatUntil)
                issueMove(PRIEST_MOVE_FOLLOW, gx, gy, 2 * BLOCK);
            return;
        }
        if (!offense) {
            // 防守期有敌人但无任何可转化目标：提前撤离（敌人来之前就撤，而非站桩被打死）
            retreatToSafe();
            return;
        }
    }

    // 仅有箭塔威胁时不能转换建筑以换取安全，先撤离射程。
    if (towerThreat) { retreatToSafe(); return; }

    // 敌军全部消失后：祭司自己血不满就优先自疗回满；满血后才治疗残血友军。治疗关系会自动持续，不重复下发。
    if (priest->NowState == HUMAN_STATE_WORKING) return;
    if (priest->Blood < priest->MaxBlood) {
        HumanAction(priestSN, priestSN);   // 自疗（内核：祭司对自身执行动作即治疗自己）
        g_priestMoveMode = PRIEST_MOVE_NONE;
        return;
    }
    int wounded = findWoundedAllySN(info, priestSN);
    if (wounded >= 0) {
        HumanAction(priestSN, wounded);
        g_priestMoveMode = PRIEST_MOVE_NONE;
        return;
    }

    /* 旧逻辑：冷却期待在安全位置不动
    if (priest->ConvertCooldown > 0) { retreatToSafe(); return; }
    */
    // 新逻辑：冷却期不再待命，进入下方"无敌人 → 基地巡逻扩视野"流程
    if (offense) {
        // 反攻目标：已探明厂区坐标（侦察兵探明），否则镜像兜底
        double siegeDR = 0, siegeUR = 0;
        bool siegeKnown = false;
        if (g_siegeKnown) { siegeDR = g_siegeKnownDR; siegeUR = g_siegeKnownUR; siegeKnown = true; }
        else if (enemySiegePos(info, siegeDR, siegeUR)) {
            g_siegeKnown = true; g_siegeKnownDR = siegeDR; g_siegeKnownUR = siegeUR; siegeKnown = true;
        }

        // 清场完成判定：厂区 25 格内无敌军 且 军队已推进到厂区附近（祭司才进场，避免落单被猎手锁）
        bool cleared = false;
        if (siegeKnown) {
            int nearEnemy = 0;
            for (const auto& e : info.enemy_armies)
                if (e.Blood > 0 && calDistance(e.DR, e.UR, siegeDR, siegeUR) <= 25 * BLOCK) nearEnemy++;
            for (const auto& f : info.enemy_farmers)
                if (f.Blood > 0 && calDistance(f.DR, f.UR, siegeDR, siegeUR) <= 25 * BLOCK) nearEnemy++;
            double armyDR = 0, armyUR = 0;
            bool hasArmy = armyCenterPos(info, armyDR, armyUR);
            bool armyAtSiege = hasArmy && calDistance(armyDR, armyUR, siegeDR, siegeUR) <= 20 * BLOCK;
            cleared = armyAtSiege && nearEnemy == 0;
        }

        if (siegeKnown && cleared) {
            // 清场完成：进场转化攻城厂（胜利条件）
            for (const auto& b : info.enemy_buildings)
                if (b.Type == BUILDING_SIEGE && b.Blood > 0) {
                    HumanAction(priestSN, b.SN);
                    g_priestMoveMode = PRIEST_MOVE_NONE;
                    return;
                }
        } else if (siegeKnown) {
            // 厂区已探明但未清场：祭司站在我方战线"背敌侧"（军队重心再往回 9 格），
            // 不贴火线、不被敌追兵缠上；仅高价值目标(投石车)在安全距离内才前出转化(见上方 C+ 段)。
            double armyDR = 0, armyUR = 0;
            if (armyCenterPos(info, armyDR, armyUR)) {
                if (calDistance(armyDR, armyUR, siegeDR, siegeUR) <= 18 * BLOCK) {
                    // 锚点 = 军队重心沿"背敌方向"再延伸 9 格；背敌方向优先取最近敌，无近敌则取厂区反方向
                    double ax = armyDR, ay = armyUR;
                    double ex = 0, ey = 0; double ndAnchor = 1e18;
                    int ne = nearestEnemyUnitSN(info, armyDR, armyUR, ndAnchor);
                    // 后退距离由 9 格收到 5 格：之前推太远，敌人出现时祭司离目标 d 过大，
                    // 更难进入 12 格转化射程（也是"总攻不转化"的诱因之一）。5 格仍能避开火线。
                    if (ne >= 0 && enemyDetailPos(info, ne, ex, ey)) {
                        double rx = armyDR - ex, ry = armyUR - ey;   // 由敌指向军队 = 背敌方向
                        double rl = std::sqrt(rx * rx + ry * ry);
                        if (rl > 1) { ax = armyDR + rx / rl * 5 * BLOCK; ay = armyUR + ry / rl * 5 * BLOCK; }
                    } else {
                        double vx = armyDR - siegeDR, vy = armyUR - siegeUR; // 厂区→军队方向(我方推进方向)
                        double vl = std::sqrt(vx * vx + vy * vy);
                        if (vl > 1) { ax = armyDR + vx / vl * 5 * BLOCK; ay = armyUR + vy / vl * 5 * BLOCK; }
                    }
                    ax = fmax(BLOCK, fmin(ax, (MAP_L - 1) * BLOCK));
                    ay = fmax(BLOCK, fmin(ay, (MAP_U - 1) * BLOCK));
                    issueMove(PRIEST_MOVE_FOLLOW, ax, ay, 3 * BLOCK);
                } else
                    retreatToSafe();   // 军队还在推进，祭司留家等清场
            } else {
                retreatToSafe();
            }
        } else {
            // 厂区未探明：祭司留家，等侦察兵探路
            retreatToSafe();
        }
    } else {
        /* 旧逻辑：无敌人 → 直接回安全位置待命（视野局限在基地内，波次部队到脸前才发现）
        retreatToSafe();
        */
        // 新逻辑（用户方案+2026-08-31 增强）：无战斗单位 → 基地周边 4 点巡逻，扩大视野提前预警波次部队。
        // 半径逐圈扩大：15 → 20 → 25 → 30 格（每绕完一圈 +5，封顶 30）。
        // 祭司视野 12 格，站 30 格路点可看到 42 格外。上限 30 格的依据：C+ 段转化目标
        // 可达上限 REACH_LIMIT=34 格，巡逻路点若超过该距离即深入敌方腹地（祭司死=失败）。
        // 路点不可走（海/建筑/越界）时向中心回缩（每次 2 格），缩到 4 格仍不可走则跳过该方向点。
        {
            static int patrolIdx = 0;      // 当前路点序号 0..3（北/东/南/西）
            static int patrolRing = 0;     // 当前圈数 0..3 → 半径 15/20/25/30
            static int patrolLastFrame = -100000;
            if (info.GameFrame - patrolLastFrame > 60) {   // 防抖 60 帧（约 2.4 秒，避免每帧下令抖路）
                int cdr = 0, cur = 0;
                if (centerBlockPos(info, cdr, cur)) {
                    static const int DX[4] = { 1, 0, -1, 0 };   // 北/东/南/西
                    static const int DY[4] = { 0, 1, 0, -1 };
                    const int idx = patrolIdx % 4;
                    int radius = 15 + patrolRing * 5;
                    int txb = cdr + DX[idx] * radius;
                    int tyb = cur + DY[idx] * radius;
                    while (radius > 4 && !isWalkable(info, txb, tyb)) {  // 海/建筑/越界 → 回缩
                        radius -= 2;
                        txb = cdr + DX[idx] * radius;
                        tyb = cur + DY[idx] * radius;
                    }
                    if (isWalkable(info, txb, tyb)) {
                        double tx = (txb + 0.5) * BLOCK;
                        double ty = (tyb + 0.5) * BLOCK;
                        // [探针] 巡逻行为确认：600 帧去重，验证祭司确实在 4 点巡逻且半径逐圈扩大
                        {
                            static int s_lastPatrolLog = -100000;
                            if (info.GameFrame - s_lastPatrolLog >= 600) {
                                s_lastPatrolLog = info.GameFrame;
                                qInfo() << "[STAT] priest_patrol frame" << info.GameFrame
                                        << "idx" << idx << "ring" << patrolRing << "radius" << radius
                                        << "tgt" << txb << tyb
                                        << "priest" << int(priest->DR / BLOCK) << int(priest->UR / BLOCK);
                            }
                        }
                        if (calDistance(priest->DR, priest->UR, tx, ty) <= 2 * BLOCK) {
                            patrolIdx++;                       // 到达路点 → 换下一个
                            if (patrolIdx % 4 == 0 && patrolRing < 3) patrolRing++;  // 绕完一圈 → 半径 +5
                        } else {
                            HumanMove(priestSN, tx, ty);
                            patrolLastFrame = info.GameFrame;
                        }
                    } else {
                        patrolIdx++;                           // 该方向整条半径都不可走 → 跳过本点
                    }
                }
            }
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

// 目标资源是否仍可采集（还在资源列表且有余量/血量，动物已死/矿已空视为失效；农田在 buildings 里）
static bool resourceStillValid(const tagInfo& info, int sn)
{
    for (const auto& r : info.resources)
        if (r.SN == sn && (r.Cnt > 0 || r.Blood > 0)) return true;
    for (const auto& b : info.buildings)
        if (b.SN == sn && b.Type == BUILDING_FARM && b.Cnt > 0) return true;
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

// 已建成（Percent>=100）建筑数量——时代升级前置/农田等需要"建成"判断
int UsrAI::countBuildingBuilt(const tagInfo& info, int type)
{
    int n = 0;
    for (const auto& b : info.buildings)
        if (b.Type == type && b.Percent >= 100) n++;
    return n;
}

// 找某类型中"未建成(Percent<100)且无人在施工"的建筑 SN（烂尾），没有则 -1
static int findUnfinishedBuilding(const tagInfo& info, int type)
{
    for (const auto& b : info.buildings) {
        if (b.Type != type || b.Percent >= 100) continue;
        bool hasWorker = false;
        for (const auto& f : info.farmers)
            if (f.FarmerSort == FARMERTYPE_FARMER && f.WorkObjectSN == b.SN) { hasWorker = true; break; }
        if (!hasWorker) return b.SN;
    }
    return -1;
}

// 某块农田是否已有人种（正在采这块田，或正站在田边工作）——防"多人种一块"
static bool farmHasFarmer(const tagInfo& info, int farmSN, double fdr, double fur)
{
    const double BLOCK = double(BLOCKSIDELENGTH);
    for (const auto& f : info.farmers) {
        if (f.FarmerSort != FARMERTYPE_FARMER) continue;
        if (f.WorkObjectSN == farmSN) return true;                    // 工作对象就是这块田（含往返途中）
        if (f.NowState == HUMAN_STATE_WORKING) {
            double dx = f.DR - fdr, dy = f.UR - fur;
            if (dx * dx + dy * dy <= 1.5 * 1.5 * BLOCK * BLOCK) return true;  // 站在田边
        }
    }
    return false;
}

// 清理失效锁定：锁主已死 或 田已耗尽/已不存在 → 释放（防永久死锁的空田）
static void pruneFarmLeases(const tagInfo& info)
{
    std::set<int> alive, validFarm;
    for (const auto& f : info.farmers) alive.insert(f.SN);
    for (const auto& b : info.buildings)
        if (b.Type == BUILDING_FARM && b.Percent >= 100 && b.Cnt > 0)
            validFarm.insert(b.SN);
    for (auto it = g_farmerFarm.begin(); it != g_farmerFarm.end(); ) {
        if (!alive.count(it->first) || !validFarm.count(it->second)) {
            g_ownedFarms.erase(it->second);
            it = g_farmerFarm.erase(it);
        } else {
            ++it;
        }
    }
}

// 有效农田数量（已建成且还有存粮）——采空的田不算，用于"还能种几块"判断
static int countValidFarm(const tagInfo& info)
{
    int n = 0;
    for (const auto& b : info.buildings)
        if (b.Type == BUILDING_FARM && b.Percent >= 100 && b.Cnt > 0) n++;
    return n;
}

// 最近有存粮且无人在种的农田 SN（供村民种田采食）
int UsrAI::nearestFarmSN(const tagInfo& info, double pr, double pu)
{
    const double BLOCK = double(BLOCKSIDELENGTH);
    int best = -1; double bd = 1e18;
    for (const auto& b : info.buildings) {
        if (b.Type != BUILDING_FARM || b.Percent < 100) continue;
        if (b.Cnt <= 0) continue;   // 农田已耗尽
        if (g_farmAssigned.count(b.SN)) continue;   // 本帧已派过人，换一块（防快照滞后双人种）
        if (g_ownedFarms.count(b.SN)) continue;     // 已被别人锁定（跨帧归属），换一块
        double fdr = (b.BlockDR + 0.5) * BLOCK, fur = (b.BlockUR + 0.5) * BLOCK;
        if (farmHasFarmer(info, b.SN, fdr, fur)) continue;   // 已有人种，换一块
        double d = calDistance(pr, pu, fdr, fur);
        if (d < bd) { bd = d; best = b.SN; }
    }
    return best;
}

// 最近敌人单位 SN（仅军队/农民，不含建筑）
int UsrAI::nearestEnemyUnitSN(const tagInfo& info, double pr, double pu, double& outDist)
{
    int best = -1; double bd = 1e18;
    for (const auto& a : info.enemy_armies) {
        if (a.Blood <= 0) continue;
        double d = calDistance(pr, pu, a.DR, a.UR);
        if (d < bd) { bd = d; best = a.SN; }
    }
    for (const auto& f : info.enemy_farmers) {
        if (f.Blood <= 0) continue;
        double d = calDistance(pr, pu, f.DR, f.UR);
        if (d < bd) { bd = d; best = f.SN; }
    }
    outDist = bd;
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

// 铜器时代且尚未探到攻城厂时，造村民/产兵都要给侦察兵预留的食物量。
// 背景：上轮 10 局实测探路成功率仅 10%（反而比改前 25% 更差），根因是人口提到 18 后
// 食物被"造村民 + 产兵"持续吃到 <60，侦察兵（60食）永远排不上队 → 训不出 → 探不到路。
// 探路是反攻获胜的前提，优先级应高于扩军，故用预留额度把侦察兵"保护"出来。
// ==================== 第三波决策：三条规则的公共判定 ====================

// 纯几何距离（AI::calDistance 是成员函数，static 自由函数调用不了，此处等价实现）
static double wave3Dist(double x1, double y1, double x2, double y2)
{
    return pow(pow(x1 - x2, 2) + pow(y1 - y2, 2), 0.5);
}

// 规则1：第三波已到（>=21000 帧）但仍在工具时代 → 进入"全力冲铜器"状态。
// 此状态下：升铜器优先级最高，禁止造村民与产兵，资源让给升级与升铜前置建筑。
static bool isWave3RushBronze(const tagInfo& info)
{
    return info.GameFrame >= WAVE3_FRAME
        && info.civilizationStage == CIVILIZATION_TOOLAGE;
}

// 规则2：敌我坐标是否处于我方任一箭塔的射程(7格)内。
// 箭塔由引擎自动索敌开火（Core_List::manageMontorAct），此处仅用于判断"该不该拉仇恨"。
static bool isInTowerRange(const tagInfo& info, double dr, double ur)
{
    const double BLOCK = double(BLOCKSIDELENGTH);
    const double RANGE = double(ARROWTOWER_RANGE_BLOCKS) * BLOCK;
    for (const auto& b : info.buildings) {
        if (b.Type != BUILDING_ARROWTOWER || b.Percent < 100) continue;
        double tdr = (b.BlockDR + 0.5) * BLOCK;
        double tur = (b.BlockUR + 0.5) * BLOCK;
        if (wave3Dist(dr, ur, tdr, tur) <= RANGE) return true;
    }
    return false;
}

// 规则3（方案A 位置分区）：判断投石车是否为"第三波推进来的"。
// 难点：wave3Units 是 enemyai.cpp 的 static，UsrAI 访问不到；tagArmy 也无波次字段。
// 且第三波的 2 台投石车是从敌方初始 6 台里"挑选"的（SelectWaveUnitsBySort），并非新建，
// 因此无法从身份区分，只能按行为近似：
//   - 已探明敌方大本营(攻城武器厂) → 距大本营 >25 格视为已出动（守军不动，会留在大本营）
//   - 未探明大本营 → 距我方市镇中心 <45 格视为已推进到我方区域
static bool isWave3StoneThrower(const tagInfo& info, const tagArmy& thrower)
{
    const double BLOCK = double(BLOCKSIDELENGTH);
    // 1. 优先锚点：敌方大本营（攻城武器厂）
    for (const auto& b : info.enemy_buildings) {
        if (b.Type != BUILDING_SIEGE) continue;
        double sdr = (b.BlockDR + 0.5) * BLOCK;
        double sur = (b.BlockUR + 0.5) * BLOCK;
        double d = wave3Dist(thrower.DR, thrower.UR, sdr, sur);
        return d > double(THROWER_WAVE3_MIN_DIST_FROM_SIEGE) * BLOCK;
    }
    // 2. 兜底锚点：我方市镇中心（未探明敌方大本营时，按"是否推进到我方区域"判定）
    for (const auto& b : info.buildings) {
        if (b.Type != BUILDING_CENTER) continue;
        double cx = (b.BlockDR + 0.5) * BLOCK;
        double cy = (b.BlockUR + 0.5) * BLOCK;
        double d = wave3Dist(thrower.DR, thrower.UR, cx, cy);
        return d < double(THROWER_WAVE3_MAX_DIST_FROM_CENTER) * BLOCK;
    }
    return false;   // 无任何锚点时保守处理：不转化
}

static int scoutFoodReserve(const tagInfo& info)
{
    // 侦察兵实际训练成本 100 食（config.json BUILDING_STABLE_CREATE_SCOUT_FOOD=100），
    // 铜器后未探路时造村民/产兵/科技都要预留 100 食给侦察兵，否则它永远排不上队
    if (info.civilizationStage < CIVILIZATION_BRONZEAGE) return 0;
    if (g_siegeKnown) return 0;
    // 熔断（方案D，2026-09-01）：侦察兵已训出且长时间(6000帧≈4分钟)仍未探明厂区 → 不再预留。
    // 根因：侦察兵卡点→厂区永久探不明→reserve 永久 +100 食→造村民/产兵/科技被拖垮（"有的图产不出兵"）。
    // 侦察兵训出后 6000 帧内要么出发探路要么阵亡重训（重训会重置 g_scoutTrainFrame，重新计时），
    // 长时间活着却没探明 = 探路卡死，此时继续预留已无意义，放归经济恢复产兵。
    if (g_scoutSN >= 0 && g_scoutTrainFrame >= 0
        && info.GameFrame - g_scoutTrainFrame > 6000) return 0;
    return 100;
}

// 升铜器前置（市场/靶场/马厩）是否已"建成"2 种（必须 Percent>=100，与升铜器判断 countBuildingBuilt 一致；
// 否则地基阶段就被误判为"前置齐"，采木配比提前下调，导致前置建筑建得更慢、升铜器被拖垮）
static bool toolBuildingsReady(const tagInfo& info)
{
    int n = 0;
    for (const auto& b : info.buildings)
        if ((b.Type == BUILDING_MARKET || b.Type == BUILDING_RANGE || b.Type == BUILDING_STABLE)
            && b.Percent >= 100)
            n++;
    return n >= 2;
}

// 轮询分配资源大类（按时代调整比例）
// 参数 idx 是跨帧递增的轮询游标（g_jobRound++，mod 10 长期均匀；不能每帧从 0 数空闲农民）
// 工具时代：优先凑 300 木建市场+靶场 → 前置齐后全力攒 800 食升铜器（探到金则顺带 1 成采金）
// 箭塔研发完成（g_towerPhase==3）且塔未满 3 座期间，石头配比提到 2 成（3 座塔共需 450 石）
// 铜器时代：食物4 黄金3 木头2 石头1（黄金是建军瓶颈）
int UsrAI::pickResourceClass(const tagInfo& info, int idx)
{
    int r = idx % 10;
    // 粮食预警：低于阈值时食物配比提到 8 成（保粮兜底，其余匀给木/石），优先恢复粮食
    if (info.Meat < FOOD_ALERT_THRESHOLD) {
        if (r < 8) return 0;
        if (r < 9) return 1;
        return 2;
    }
    if (info.civilizationStage >= CIVILIZATION_BRONZEAGE) {
        /* 旧逻辑：误以为金矿在岛上采不到，铜器不派采金（黄金150封顶）
        if (r < 5) return 0;   // 食物5
        if (r < 9) return 1;   // 木4
        return 2;              // 石1
        */
        // 新逻辑：金矿确认陆地可达（BFS 验证 72 个全连通，最近 30 格），铜器派 3 成采金。
        // 黄金是方阵/复合弓/阔剑的命脉，采金效率低（往返损耗）必须足额分配。
        if (r < 4) return 0;   // 食物4
        if (r < 7) return 3;   // 金3（4,5,6）
        if (r < 9) return 1;   // 木2（7,8）
        return 2;              // 石1（9）
    }
    // 箭塔建塔要 150 石/座：石头固定 2 成（不再依赖研发状态），保证研发完成时石头已攒够
    // 工具时代
    if (!toolBuildingsReady(info)) {
        /* 旧逻辑1（v1）：前置未齐木 5 成优先，食物只 4 成
        if (r < 4) return 0;   // 食物4
        if (r < 9) return 1;   // 木5（4,5,6,7,8）
        return 2;              // 石1（9）
        */
        /* 旧逻辑2（v2）：食 6 成 / 木 3 成——实测升铜 8.5 分钟，木头成了瓶颈（425 木太慢）
        if (r < 6) return 0;   // 食物6
        if (r < 9) return 1;   // 木3（6,7,8）
        return 2;              // 石1（9）
        */
        // 新逻辑（v3 动态配比·阶段1）：前置期（兵营+市场+靶场未齐）→ **木 5 成**。
        // 前置链固定 425 木（兵营125+市场150+靶场150，靶场/马厩均需兵营前置），
        // 木才是升铜最大瓶颈：6 人采木 3 木/秒 → 425 木仅 142 秒；食物 4 成够维持造村民。
        if (r < 4) return 0;   // 食物4
        if (r < 9) return 1;   // 木5（4,5,6,7,8）
        return 2;              // 石1（9）
    }
    /* 旧逻辑1：工具时代默认食5木3石2
    if (r < 5) return 0;
    if (r < 8) return 1;
    return 2;
    */
    /* 旧逻辑2（v2）：前置已齐食 6 木 3 石 1
    if (r < 6) return 0;   // 食物6
    if (r < 9) return 1;   // 木3
    return 2;              // 石1
    */
    // 新逻辑（v3 动态配比·阶段2）：前置已齐 → **食 8 成**全力攒 800 食升铜（木/石各 1 成保建筑）。
    // 10 人采食 4 食/秒 → 1000 食（800升铜+200造人）约 250 秒。目标：升铜压到 6.5~7 分钟。
    if (r < 8) return 0;   // 食物8
    if (r < 9) return 1;   // 木1（8）
    return 2;              // 石1（9）
}

// 造村民 + 空闲村民派工
void UsrAI::controlEconomy(const tagInfo& info)
{
    int farmers = countFarmers(info);
    // 经济人口封顶：工具时代 16、铜器时代 18。上轮 14 人采木人手不足，升铜器前置建筑建太慢，
    // 是升铜器 50% 失败的主因；提到 16 人让木头/食物双线都能攒起来，升铜器更快更稳。
    /* 旧逻辑：工具16/铜器18（人口多采食快，但升铜前吃食物拖慢 800 食积累）
    int target = (info.civilizationStage >= CIVILIZATION_BRONZEAGE) ? 18 : 16;
    */
    // 新逻辑（用户方案）：升铜前 12 人（8 初始+4 新增），把食物让给升铜器（800 食）；
    // 升铜后再扩到 16（采金+采食+采木）。目标：5~9 分钟升铜。
    int target = (info.civilizationStage >= CIVILIZATION_BRONZEAGE) ? 16 : 12;

    // 1. 市镇中心产村民（升铜器条件满足时暂停产村民，把市中心与食物让给升级）
    // 阈值用 700 而非 500：开局食物就是 500，若用 500 前置一建成立刻暂停造村民，人口卡在 12，
    // 12 人采食太慢 → 升铜器拖到 13 分钟、升铜后食物见底、侦察兵训不出（上轮实测根因）。
    // 用 700 让人口先造到接近 16，再暂停攒最后 100 食升铜器。
    bool readyUpgrade = false;
    if (info.civilizationStage == CIVILIZATION_TOOLAGE && info.Meat >= 700) {
        int tb = (countBuildingBuilt(info, BUILDING_MARKET) > 0)
               + (countBuildingBuilt(info, BUILDING_RANGE) > 0)
               + (countBuildingBuilt(info, BUILDING_STABLE) > 0);
        readyUpgrade = (tb >= 2);
    }
    // 铜器后未探路时，造村民也要预留 100 食给侦察兵（实际成本 100，否则人口扩张会把侦察兵饿死，探路永远失败）
    // 规则1：第三波已到但仍在工具时代 → 禁止造村民，食物让给升铜器
    const int farmerScoutReserve = scoutFoodReserve(info);
    const bool forbidFarmer = isWave3RushBronze(info);
    for (const auto& b : info.buildings) {
        if (b.Type == BUILDING_CENTER && b.Percent >= 100 && b.Project == ACT_NULL
            && farmers < target && info.Human_Num < info.Human_MaxNum
            && info.Meat >= 50 + farmerScoutReserve
            && !readyUpgrade && !forbidFarmer && !g_assigned.count(b.SN)) {
            BuildingAction(b.SN, BUILDING_CENTER_CREATEFARMER);
            g_assigned.insert(b.SN);
        }
    }

    // 2. 空闲村民派工（跳过本帧已派活的）
    // 工种轮询游标 g_jobRound 跨帧持续递增：农民交错回城时每帧只有 1~5 个 IDLE，
    // 若每帧从 0 数 idx，空闲农民恒拿 0~5 → 全员漂移到食物，木/石/金永久流失。
    // 游标持续 +1（mod 10）则长期分布均匀，20 农民稳定 12 食物/6 木/2 石。
    for (const auto& f : info.farmers) {
        if (f.FarmerSort != FARMERTYPE_FARMER || f.NowState != HUMAN_STATE_IDLE) continue;
        if (g_assigned.count(f.SN)) continue;
        int sn = -1;
        // 优先沿用上次工作目标（职业稳定），目标资源耗尽/失效才重新轮询分配
        if (g_farmerTargetSN.count(f.SN) && resourceStillValid(info, g_farmerTargetSN[f.SN])) {
            sn = g_farmerTargetSN[f.SN];
        } else {
            int cls = pickResourceClass(info, g_jobRound++);
            if (cls == 0) {
                // 食物：先回自己锁定的田（战斗/交粮后自动恢复），无锁才找新田；再无则浆果/猎物
                int myFarm = (g_farmerFarm.count(f.SN)) ? g_farmerFarm[f.SN] : -1;
                bool valid = false;
                for (const auto& b : info.buildings) {
                    if (b.SN == myFarm && b.Type == BUILDING_FARM && b.Percent >= 100 && b.Cnt > 0) {
                        valid = true; break;
                    }
                }
                if (valid) {
                    sn = myFarm;
                } else {
                    sn = nearestFarmSN(info, f.DR, f.UR);
                    if (sn >= 0) {
                        g_farmAssigned.insert(sn);      // 本帧已派工，防同帧双人种一块
                        g_farmerFarm[f.SN] = sn;         // 锁定新田（一田一农）
                        g_ownedFarms.insert(sn);
                    } else {
                        sn = nearestResourceSN(info, f.DR, f.UR, 0);   // 无田可种 → 浆果/猎物
                    }
                }
            } else {
                sn = nearestResourceSN(info, f.DR, f.UR, cls);
            }
            // 降级搜索：目标类别无资源时，遍历其他类别找一个有资源的（防止村民采集完站着不动）
            if (sn < 0) {
                for (int fallback = 0; fallback < 4; fallback++) {
                    sn = nearestResourceSN(info, f.DR, f.UR, fallback);
                    if (sn >= 0) break;
                }
                if (sn < 0) sn = nearestFarmSN(info, f.DR, f.UR);  // 最后尝试农田
            }
            if (sn >= 0) g_farmerTargetSN[f.SN] = sn;   // 记录新目标
        }
        if (sn >= 0) {
            HumanAction(f.SN, sn);
            g_assigned.insert(f.SN);
        }
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

// 找可建造平地（螺旋搜索，排除重叠与上次成功建造位；maxRadius 限制离中心的搜索半径）
// cx<0 表示以市镇中心为搜索中心；outward=true 时从 maxRadius 往内选（优先远处空位，防扎堆市中心）
bool UsrAI::findBuildPos(const tagInfo& info, int buildNum, int& bdr, int& bur, int maxRadius, int cx, int cy, bool outward)
{
    int size = (buildNum == BUILDING_HOME || buildNum == BUILDING_ARROWTOWER) ? 2 : 3;
    const double BLOCK = double(BLOCKSIDELENGTH);
    int cdr = cx, cur = cy;
    if (cx < 0 || cy < 0) {
        if (!centerBlockPos(info, cdr, cur)) return false;
    }

    // 候选区域是否与已有建筑/单位/资源重叠（建筑 BlockDR/BlockUR 为占地下角，向右上扩展）
    // 建筑外扩 3 格缓冲（"相邻3格"间隔，防互相卡位）；资源（树/果丛/金矿/石矿/动物）占地也一并
    // 标记，避免选到障碍位导致 HumanBuild 失败反复重试。
    auto occupied = [&](int i, int j) -> bool {
        const int M = 3;   // 建筑间隔缓冲 3 格
        for (const auto& b : info.buildings) {
            int bs = (b.Type == BUILDING_HOME || b.Type == BUILDING_ARROWTOWER) ? 2 : 3;
            if (i - M < b.BlockDR + bs && b.BlockDR < i + size + M &&
                j - M < b.BlockUR + bs && b.BlockUR < j + size + M) return true;
        }
        // 资源/障碍占地（1 格外扩 1 格）
        for (const auto& r : info.resources) {
            if (r.Cnt <= 0 && r.Blood <= 0) continue;
            int tb = (int)(r.DR / BLOCK), tu = (int)(r.UR / BLOCK);
            if (i - 1 < tb + 1 && tb < i + size + 1 &&
                j - 1 < tu + 1 && tu < j + size + 1) return true;
        }
        for (const auto& f : info.farmers)
            if (i <= f.BlockDR && f.BlockDR < i + size && j <= f.BlockUR && f.BlockUR < j + size) return true;
        for (const auto& a : info.armies)
            if (i <= a.BlockDR && a.BlockDR < i + size && j <= a.BlockUR && a.BlockUR < j + size) return true;
        return false;
    };

    // outward：从远到近散开选址——每环 16 个角度采样，起点随建筑序号旋转，
    // 不同建筑落在环上不同方向（若整环都占满则收半径往内，逐环尝试）
    if (outward) {
        for (int r = maxRadius; r >= 2; r--) {
            for (int k = 0; k < 16; k++) {
                double ang = ((k * 3 + g_buildSeq * 7) % 16) * (2 * 3.14159265358979 / 16.0);
                int i = cdr + (int)std::lround(r * std::cos(ang));
                int j = cur + (int)std::lround(r * std::sin(ang));
                if (i < 0 || j < 0 || i + size > MAP_L || j + size > MAP_U) continue;
                if (!isFlatArea(info, i, j, size)) continue;
                if (occupied(i, j)) continue;
                if (i == g_lastBuildDR && j == g_lastBuildUR && size == g_lastBuildSize) continue;
                if (g_frameBuildPos.count(std::make_pair(i, j))) continue;
                g_frameBuildPos.insert(std::make_pair(i, j));
                bdr = i; bur = j;
                return true;
            }
        }
        return false;
    }

    for (int r = 2; r <= maxRadius; r++) {
        for (int i = cdr - r; i <= cdr + r; i++) {
            for (int j = cur - r; j <= cur + r; j++) {
                if (i < 0 || j < 0 || i + size > MAP_L || j + size > MAP_U) continue;   // 越界
                if (!isFlatArea(info, i, j, size)) continue;
                if (occupied(i, j)) continue;                          // 排除重叠
                if (i == g_lastBuildDR && j == g_lastBuildUR && size == g_lastBuildSize) continue;  // 跳过上次已建位
                if (g_frameBuildPos.count(std::make_pair(i, j))) continue;   // 同帧已选位（防同帧两建筑重叠）
                g_frameBuildPos.insert(std::make_pair(i, j));
                bdr = i; bur = j;
                return true;
            }
        }
    }
    return false;
}

// 建筑顺序 + 升铜器 + 科技
void UsrAI::controlBuilding(const tagInfo& info)
{
    // 升铜资源已交付（市镇中心开始升级 或 已进入铜器时代）：
    // 用户方案——全力攒资源升铜，交付前除"箭塔 + 升铜前置2座(引擎硬性要求)"外不建任何建筑。
    bool bronzeCommitted = false;
    if (info.civilizationStage >= CIVILIZATION_BRONZEAGE) bronzeCommitted = true;
    for (const auto& b : info.buildings)
        if (b.Type == BUILDING_CENTER && b.Project == BUILDING_CENTER_UPGRADE)
            bronzeCommitted = true;

    auto tryBuild = [&](int buildNum) -> bool {
        int bdr = 0, bur = 0;
        // 农田贴谷仓建（物资运送近）；箭塔贴市中心 12 格护住祭司；
        // 升铜前置/军事建筑（马厩/市场/靶场/兵营）近处选址保证建造速度（升铜节奏不能拖）；
        // 房屋/仓库等 outward 散开，避免扎堆市中心导致后期选址失败/建筑重叠
        if (buildNum == BUILDING_FARM) {
            int gdr = -1, gur = -1;
            for (const auto& b : info.buildings)
                if (b.Type == BUILDING_GRANARY) { gdr = b.BlockDR; gur = b.BlockUR; break; }
            if (!findBuildPos(info, buildNum, bdr, bur, 16, gdr, gur, true)
                && !findBuildPos(info, buildNum, bdr, bur, 16, gdr, gur, false)
                && !findBuildPos(info, buildNum, bdr, bur, 24)) return false;
        } else if (buildNum == BUILDING_ARROWTOWER) {
            /* 旧逻辑：以市镇中心为中心 12 格内建塔（祭司巡逻/转化时可能远离塔，护不住）
            if (!findBuildPos(info, buildNum, bdr, bur, 12)
                && !findBuildPos(info, buildNum, bdr, bur, 24)) return false;
            */
            // 新逻辑（用户方案）：以**祭司当前所在位置**为中心建塔——箭塔贴身护祭司。
            // 拉仇恨原理：箭塔开火后其 Project 记录攻击目标，敌方 FindThreatToArmy 查到
            // "箭塔在打我" 就把仇恨从祭司转到箭塔。塔在祭司身边 = 追兵必撞进塔的射程。
            // 祭司不存在/找不到时回退市中心；贴身近处优先（outward=false），再远处，再市中心兜底。
            {
                const double BLOCK = double(BLOCKSIDELENGTH);
                int pdr = -1, pur = -1;
                const int psn = findPriestSN(info);
                if (psn >= 0) {
                    for (const auto& a : info.armies)
                        if (a.SN == psn) { pdr = (int)(a.DR / BLOCK); pur = (int)(a.UR / BLOCK); break; }
                }
                bool ok = false;
                if (pdr >= 0 && pur >= 0) {
                    ok = findBuildPos(info, buildNum, bdr, bur, 12, pdr, pur, false)   // 祭司近处优先
                      || findBuildPos(info, buildNum, bdr, bur, 12, pdr, pur, true)    // 祭司外围
                      || findBuildPos(info, buildNum, bdr, bur, 24);                   // 市中心兜底
                } else {
                    ok = findBuildPos(info, buildNum, bdr, bur, 12)
                      || findBuildPos(info, buildNum, bdr, bur, 24);
                }
                if (!ok) return false;
            }
        } else if (buildNum == BUILDING_STABLE || buildNum == BUILDING_MARKET
                   || buildNum == BUILDING_RANGE || buildNum == BUILDING_ARMYCAMP) {
            // 关键前置：近处选址（内向螺旋），保证建造速度
            if (!findBuildPos(info, buildNum, bdr, bur, 24)
                && !findBuildPos(info, buildNum, bdr, bur, 36)) return false;
        } else if (!findBuildPos(info, buildNum, bdr, bur, 14, -1, -1, true)
                   && !findBuildPos(info, buildNum, bdr, bur, 24)) {
            return false;
        }
        for (const auto& f : info.farmers) {
            if (f.FarmerSort != FARMERTYPE_FARMER || f.NowState != HUMAN_STATE_IDLE) continue;
            if (g_buildAssigned.count(f.SN)) continue;   // 本帧已被其他 tryBuild 派去建造，换一个农民
            if (g_assigned.count(f.SN)) continue;        // 本帧已被派工（采集等），不抢，避免指令被顶
            HumanBuild(f.SN, buildNum, bdr, bur);
            g_assigned.insert(f.SN);
            g_buildAssigned.insert(f.SN);                // 记录，防同帧抢同一个农民
            g_buildDispatch[buildNum] = f.SN;            // 记录在途建造，防跨帧重复抢建
            g_lastBuildDR = bdr; g_lastBuildUR = bur;
            g_lastBuildSize = (buildNum == BUILDING_HOME || buildNum == BUILDING_ARROWTOWER) ? 2 : 3;
            g_buildSeq++;                                // 下一栋建筑旋转角度，落不同方向
            return true;
        }
        return false;
    };
    // 空闲建筑（Percent>=100 && 无项目）执行建筑动作
    auto idleBuilding = [&](int type, int act, int meatNeed, int woodNeed, int stoneNeed, int goldNeed) {
        for (const auto& b : info.buildings) {
            if (b.Type == type && b.Percent >= 100 && b.Project == ACT_NULL
                && info.Meat >= meatNeed && info.Wood >= woodNeed
                && info.Stone >= stoneNeed && info.Gold >= goldNeed) {
                if (g_assigned.count(b.SN)) continue;   // 本帧已被下过指令（如训练），避免被顶
                BuildingAction(b.SN, act);
                g_assigned.insert(b.SN);
                return true;
            }
        }
        return false;
    };
    // 科技研发状态机：观察到"Project 进入研发 → 释放"才算研发成功；下发后超时（600帧）未观察到
    // = 指令被拒（资源被抢等），自动重发。杜绝"研发失败但标志置位"→ 训练被锁刷屏（错误码 12）
    auto researchTech = [&](int buildType, int act, int meatNeed, int woodNeed, int stoneNeed, int goldNeed,
                            TechWatch& w, bool& done) {
        bool inResearch = false;
        for (const auto& b : info.buildings)
            if (b.Type == buildType && b.Project == act) { inResearch = true; break; }
        if (inResearch) { w.researching = true; w.frame = info.GameFrame; return; }  // 研发中
        if (w.researching) { done = true; w.researching = false; return; }            // Project 释放=研发完成
        if (info.GameFrame - w.frame > 600) {                                          // 超时未观察到=失败，重发
            if (idleBuilding(buildType, act, meatNeed, woodNeed, stoneNeed, goldNeed))
                w.frame = info.GameFrame;
        }
    };
    // 建单一建筑：已建成跳过；有烂尾地基则派村民修复续建；无则新建；有农民在途则等待（防跨帧抢建）
    auto ensureBuild = [&](int buildNum) -> bool {
        if (countBuildingBuilt(info, buildNum) >= 1) {           // 已建成
            g_buildDispatch.erase(buildNum);
            return true;
        }
        if (countBuilding(info, buildNum) >= 1) {                // 地基已放下（含施工中）
            g_buildDispatch.erase(buildNum);
            int unfinished = findUnfinishedBuilding(info, buildNum);
            if (unfinished >= 0) {                               // 烂尾 → 派村民修复续建
                for (const auto& f : info.farmers) {
                    if (f.FarmerSort != FARMERTYPE_FARMER || f.NowState != HUMAN_STATE_IDLE) continue;
                    if (g_assigned.count(f.SN)) continue;
                    HumanAction(f.SN, unfinished);               // FixBuilding 续建
                    g_assigned.insert(f.SN);
                    return true;
                }
            }
            return true;                                         // 有地基且正在施工，无需新建
        }
        if (g_buildDispatch.count(buildNum)) {                   // 已有农民在途
            int sn = g_buildDispatch[buildNum];
            bool stillBuilding = false;
            for (const auto& f : info.farmers)
                if (f.SN == sn && f.NowState != HUMAN_STATE_IDLE) { stillBuilding = true; break; }
            if (stillBuilding) return false;                     // 还在去建/施工中，不重复派
            g_buildDispatch.erase(buildNum);                     // 农民变 IDLE（建造失败）→ 清理并重试
        }
        return tryBuild(buildNum);                               // 新建
    };

    // ===== 规则1：第三波已到（>=21000帧）但仍在工具时代 → 全力冲铜器 =====
    // 优先级：升铜器 > 建齐升铜前置(马厩/市场/靶场) > 一切其他建筑。
    // 期间禁止造村民与产兵（见 controlEconomy / controlMilitary），资源全部让给升级与前置建筑。
    if (isWave3RushBronze(info)) {
        int req = (countBuildingBuilt(info, BUILDING_MARKET) > 0)
                + (countBuildingBuilt(info, BUILDING_RANGE) > 0)
                + (countBuildingBuilt(info, BUILDING_STABLE) > 0);
        // 1) 前置已齐 + 800 食 → 直接升铜器，本帧不再排任何命令
        if (req >= 2 && info.Meat >= 800) {
            for (const auto& b : info.buildings) {
                if (b.Type != BUILDING_CENTER || b.Percent < 100 || b.Project != ACT_NULL) continue;
                if (g_assigned.count(b.SN)) continue;
                BuildingAction(b.SN, BUILDING_CENTER_UPGRADE);
                g_assigned.insert(b.SN);
                return;
            }
        }
        // 2) 前置不足 → 木头全部投给前置建筑（按 马厩→市场→靶场 顺序，凑够 2 座即止）
        if (req < 2) {
            if (countBuilding(info, BUILDING_STABLE) < 1 && info.Wood >= 150) { ensureBuild(BUILDING_STABLE); return; }
            if (countBuilding(info, BUILDING_MARKET) < 1 && info.Wood >= 150) { ensureBuild(BUILDING_MARKET); return; }
            if (countBuilding(info, BUILDING_RANGE) < 1 && info.Wood >= 150) { ensureBuild(BUILDING_RANGE); return; }
        }
        // 3) 前置已齐但食物不足 800 → 直接返回，让食物自然累积（不建任何耗木/耗食的建筑）
        return;
    }

    /* 旧逻辑：人口余量<=4 就建房屋（上限10座）——升铜前吃 60 木/座，拖慢前置建筑
    // 1. 房屋：预留 4 个槽位，避免训练/转化把人口卡满；上限保持适中，把资源让给时代和科技。
    if (info.Human_MaxNum - info.Human_Num <= 4 && countBuilding(info, BUILDING_HOME) < 10 && info.Wood >= 60)
        tryBuild(BUILDING_HOME);
    */
    // 新逻辑（用户方案）：升铜资源交付前不建房屋——人口靠初始 2 房屋的 12 上限（正合升铜前人口目标）；
    // 升铜后才按人口余量补建。
    if (bronzeCommitted && info.Human_MaxNum - info.Human_Num <= 4
        && countBuilding(info, BUILDING_HOME) < 10 && info.Wood >= 60) {
        tryBuild(BUILDING_HOME);
        static int s_lastHouseBronzeLog = -100000;   // 探针：确认铜器时代补房分支触发（600帧去重）
        if (info.GameFrame - s_lastHouseBronzeLog >= 600) {
            s_lastHouseBronzeLog = info.GameFrame;
            qInfo() << "[STAT] house_bronze frame" << info.GameFrame
                    << "homes" << countBuilding(info, BUILDING_HOME);
        }
    }

    // 工具时代：3 座箭塔建成后补 1 座房屋（初始 2 + 此 1 = 3，人口上限 12→18），
    // 抬升铜前人口天花板，让守军/侦察兵能训出来（用户方案：塔 3 座，之后补 1 房）。
    // 不抢升铜资源：箭塔科技完成且 3 塔就位后才建，此时升铜前置木已花完、木转为富余。
    if (!bronzeCommitted && countBuilding(info, BUILDING_HOME) < 3
        && countBuilding(info, BUILDING_ARROWTOWER) >= 3
        && info.Wood >= 60) {
        tryBuild(BUILDING_HOME);
        static int s_lastHouseToolLog = -100000;   // 探针：确认工具时代补房分支触发（600帧去重）
        if (info.GameFrame - s_lastHouseToolLog >= 600) {
            s_lastHouseToolLog = info.GameFrame;
            qInfo() << "[STAT] house_toolage frame" << info.GameFrame
                    << "homes" << countBuilding(info, BUILDING_HOME);
        }
    }

    /* 旧逻辑：木>=125 就建兵营
    // 2. 兵营（开局没有）
    if (info.Wood >= 125)
        ensureBuild(BUILDING_ARMYCAMP);
    */
    // 新逻辑（用户方案修正）：兵营是升铜前置链的**引擎必需环节**——靶场/马厩的前置建筑
    // （Development.cpp 硬性要求，不建兵营则靶场/马厩永远解锁不了 → 升铜死锁）。
    // 所以兵营必须保留（125 木），只是升铜后它才用于产兵。
    if (info.Wood >= 125)
        ensureBuild(BUILDING_ARMYCAMP);

    // 2b. 仓库延后到铜器时代（120 木非升铜器必需，且近战+2 科技要 120 金前期研不起；
    //    工具时代先省下这 120 木，集中建马厩+市场凑够升铜器前置）

    // 升铜器是最高资源优先级。此处直接返回，确保本帧不会再排入任何会消耗食物的研发/训练命令。
    int bronzeRequirements = (countBuildingBuilt(info, BUILDING_MARKET) > 0)
                           + (countBuildingBuilt(info, BUILDING_RANGE) > 0)
                           + (countBuildingBuilt(info, BUILDING_STABLE) > 0);
    if (info.civilizationStage == CIVILIZATION_TOOLAGE && bronzeRequirements >= 2 && info.Meat >= 800) {
        for (const auto& b : info.buildings) {
            if (b.Type != BUILDING_CENTER || b.Percent < 100 || b.Project != ACT_NULL) continue;
            if (g_assigned.count(b.SN)) continue;
            BuildingAction(b.SN, BUILDING_CENTER_UPGRADE);
            g_assigned.insert(b.SN);
            return;
        }
    }

    // 3. 箭塔：谷仓研发「建造箭塔」（TOOLAGE，50食/10秒）→ 建塔（150石/座）。
    // 开局自带谷仓；状态机防"研发期反复建未解锁塔"（原版 towerResearched 指令瞬间置位会丢科技）
    {
        bool researching = false;
        for (const auto& b : info.buildings)
            if (b.Type == BUILDING_GRANARY && b.Project == BUILDING_GRANARY_ARROWTOWER)
                researching = true;
        if (g_towerPhase == 0 && info.Meat >= 60) {
            // Meat>=60：给市中心造农民（同帧 50食）留余量，研发本身只需 50 食
            for (const auto& b : info.buildings) {
                if (b.Type == BUILDING_GRANARY && b.Percent >= 100 && b.Project == ACT_NULL) {
                    if (g_assigned.count(b.SN)) continue;   // 谷仓本帧已被占，避免指令被顶
                    BuildingAction(b.SN, BUILDING_GRANARY_ARROWTOWER);
                    g_assigned.insert(b.SN);
                    g_towerPhase = 1;
                    g_towerWaitFrame = info.GameFrame;
                    break;
                }
            }
        } else if (g_towerPhase == 1) {
            if (researching) { g_towerPhase = 2; g_towerStartFrame = info.GameFrame; }  // 研发开始了
            else if (info.GameFrame - g_towerWaitFrame > 300) g_towerPhase = 0;   // 5秒未开始（食物被挪用）→重试
        } else if (g_towerPhase == 2) {
            // 研发中 Project 恒为科技 ID；变回 ACT_NULL 分两种：完成 或 被打断。
            // 已进行 ≥5 秒才认完成（研发耗时 10 秒基准，快进也不至于 5 秒内结束）；<5 秒变空 → 打断重试
            if (!researching && info.GameFrame - g_towerStartFrame > 300) { g_towerPhase = 3; towerResearched = true; }
            else if (!researching) g_towerPhase = 0;   // 研发中途被打断 → 重来
        }
        // 铜器先强化已有箭塔，再继续扩塔；避免“多造兵/多造塔”抢走关键科技资源。
        bool towerUpgradeStarted = false;
        if (info.civilizationStage >= CIVILIZATION_BRONZEAGE && g_towerPhase == 3 && !g_towerUpgradeResearched) {
            towerUpgradeStarted = idleBuilding(BUILDING_GRANARY, BUILDING_GRANARY_ARROWTOWE_UPGRADE,
                                               BUILDING_GRANARY_UPGRADE_ARROWTOWER_FOOD, 0,
                                               BUILDING_GRANARY_UPGRADE_ARROWTOWER_STONE, 0);
            if (towerUpgradeStarted) g_towerUpgradeResearched = true;
        }

        // 用户方案：工具时代固定 3 座箭塔（不再受击扩到 5，牺牲部分早期覆盖换升铜前人口/军队空间）；
        // 铜器后 max(3, 已建) 仍以 3 为地板，仅在被拆到 3 座以下时补建（够用即可）
        const int towerLimit = (info.civilizationStage >= CIVILIZATION_BRONZEAGE)
            ? std::max(3, countBuildingBuilt(info, BUILDING_ARROWTOWER))
            : 3;
        // 第三波(21000帧)之后彻底停建箭塔（用户方案：总攻阶段造塔无意义，且此前实测第三波后仍建塔属浪费）
        if (info.GameFrame < WAVE3_FRAME && !towerUpgradeStarted && g_towerPhase == 3 && info.Stone >= 150) {
            int built = countBuildingBuilt(info, BUILDING_ARROWTOWER);   // 已建成
            int total = countBuilding(info, BUILDING_ARROWTOWER);        // 含在建/烂尾

            // 清理在途记录：农民已放地基（total>built）或失败变空闲 → 清除
            if (g_buildDispatch.count(BUILDING_ARROWTOWER)) {
                int sn = g_buildDispatch[BUILDING_ARROWTOWER];
                bool busy = false;
                for (const auto& f : info.farmers)
                    if (f.SN == sn && f.NowState != HUMAN_STATE_IDLE) { busy = true; break; }
                if (total > built || !busy) g_buildDispatch.erase(BUILDING_ARROWTOWER);
            }

            if (built < towerLimit) {
                int unfinished = findUnfinishedBuilding(info, BUILDING_ARROWTOWER);
                if (unfinished >= 0) {                          // 烂尾 → 派村民续建
                    for (const auto& f : info.farmers) {
                        if (f.FarmerSort != FARMERTYPE_FARMER || f.NowState != HUMAN_STATE_IDLE) continue;
                        if (g_assigned.count(f.SN)) continue;
                        HumanAction(f.SN, unfinished);
                        g_assigned.insert(f.SN);
                        // [日志探针] 续建烂尾箭塔（600 帧去重）
                        static int s_lastTowerContLog = -100000;
                        if (info.GameFrame - s_lastTowerContLog >= 600) {
                            s_lastTowerContLog = info.GameFrame;
                            qInfo() << "[STAT] tower_build frame" << info.GameFrame << "action continue";
                        }
                        break;
                    }
                } else if (total == built && !g_buildDispatch.count(BUILDING_ARROWTOWER)) {
                    tryBuild(BUILDING_ARROWTOWER);              // 无在建、无在途 → 新建一座
                    // [日志探针] 新建箭塔（600 帧去重，避免每帧重试刷屏）
                    static int s_lastTowerNewLog = -100000;
                    if (info.GameFrame - s_lastTowerNewLog >= 600) {
                        s_lastTowerNewLog = info.GameFrame;
                        qInfo() << "[STAT] tower_build frame" << info.GameFrame << "action new";
                    }
                }
            }
        }
    }

    // 4. 马厩（工具时代就建：升铜器前置 + 侦察兵/骑兵训练场，优先级最高——
    //    侦察兵探路是反攻的前提，马厩建不成则侦察兵永远训不出；不依赖兵营，木够就建）
    if (info.Wood >= 150)
        ensureBuild(BUILDING_STABLE);

    // 5. 市场（升铜器前置 1 + 农田前置）
    if (info.Wood >= 150)
        ensureBuild(BUILDING_MARKET);

    // 6. 靶场（弓箭手，木够就建）
    if (info.Wood >= 150)
        ensureBuild(BUILDING_RANGE);

    /* 旧逻辑：市场建成即建农田（工具3块/铜器6块）——75木/座 + 占农民，前期木头紧张拖慢升铜
    {
        // 工具时代农田上限 3，铜器时代 6 块。粮食预警 +2 保粮兜底。
        int farmLimit = (info.civilizationStage >= CIVILIZATION_BRONZEAGE) ? 6 : 3;
        if (info.Meat < FOOD_ALERT_THRESHOLD) farmLimit += 2;   // 粮食预警：上限 +2 紧急保粮
        int unfinished = findUnfinishedBuilding(info, BUILDING_FARM);
        if (unfinished >= 0) {                                   // 有烂尾农田 → 派村民修复续建
            for (const auto& f : info.farmers) {
                if (f.FarmerSort != FARMERTYPE_FARMER || f.NowState != HUMAN_STATE_IDLE) continue;
                if (g_assigned.count(f.SN)) continue;
                HumanAction(f.SN, unfinished);
                g_assigned.insert(f.SN);
                break;
            }
        } else if (countBuildingBuilt(info, BUILDING_MARKET) >= 1
                   && countValidFarm(info) < farmLimit
                   && countBuilding(info, BUILDING_FARM) < farmLimit * 2   // 防废弃田无限累积
                   && info.Wood >= 75) {
            tryBuild(BUILDING_FARM);                             // 新建
        }
    }
    */
    // 7. 农田（新逻辑，用户方案 v2）：**升铜资源交付后**才建（不是 15 分钟后——交付即算"升铜后"）；
    //    升铜前靠瞪羚/浆果（全图约 11000 食物）完全不建农田，省 75 木/座全力冲升铜。
    {
        int farmLimit = (info.civilizationStage >= CIVILIZATION_BRONZEAGE) ? 6 : 3;
        /* 旧逻辑：15 分钟后才允许建田
        bool farmTime = (info.GameFrame > 22500);
        */
        bool farmTime = bronzeCommitted;                         // 升铜资源已交付 → 可建田
        if (info.Meat < FOOD_ALERT_THRESHOLD) { farmLimit += 2; farmTime = true; }  // 粮食预警：紧急保粮
        int unfinished = findUnfinishedBuilding(info, BUILDING_FARM);
        if (unfinished >= 0 && farmTime) {                       // 有烂尾农田 → 派村民修复续建
            for (const auto& f : info.farmers) {
                if (f.FarmerSort != FARMERTYPE_FARMER || f.NowState != HUMAN_STATE_IDLE) continue;
                if (g_assigned.count(f.SN)) continue;
                HumanAction(f.SN, unfinished);
                g_assigned.insert(f.SN);
                break;
            }
        } else if (farmTime
                   && countBuildingBuilt(info, BUILDING_MARKET) >= 1
                   && countValidFarm(info) < farmLimit
                   && countBuilding(info, BUILDING_FARM) < farmLimit * 2   // 防废弃田无限累积
                   && info.Wood >= 75) {
            tryBuild(BUILDING_FARM);                             // 新建
        }
    }

    // 8. 战斧科技（工具时代科技，兵营建成后研发：棍棒→斧头，100食）
    if (!g_swordResearched && countBuildingBuilt(info, BUILDING_ARMYCAMP) >= 1) {
        if (idleBuilding(BUILDING_ARMYCAMP, BUILDING_ARMYCAMP_UPGRADE_CLUBMAN, 100, 0, 0, 0))
            g_swordResearched = true;
    }

    // 9. 仓库近战+2 科技：100 食 + 120 金；黄金≥200 才研发（留 80 金给 2 个方阵兵）
    if (!g_meleeResearched && countBuildingBuilt(info, BUILDING_STOCK) >= 1 && info.Gold >= 200) {
        if (idleBuilding(BUILDING_STOCK, BUILDING_STOCK_UPGRADE_USETOOL, 100, 0, 0, 120))
            g_meleeResearched = true;
    }

    // 9b. 木材加工（市场，工具时代）：远程攻击距离+1 & 伐木+2，远程兵核心科技（120食75木）
    if (!g_woodUpgradeResearched && countBuildingBuilt(info, BUILDING_MARKET) >= 1) {
        if (idleBuilding(BUILDING_MARKET, BUILDING_MARKET_WOOD_UPGRADE, 120, 75, 0, 0))
            g_woodUpgradeResearched = true;
    }

    // ===== 铜器时代 =====
    if (info.civilizationStage >= CIVILIZATION_BRONZEAGE) {
        // 9c. 仓库（延后到铜器再建：近战+2 科技 + 工具使用科技；升铜器后木头压力已缓）
        if (info.Wood >= 120)
            ensureBuild(BUILDING_STOCK);

        // 10. 学院（方阵兵，前置=马厩建成；马厩已在工具时代建好，铜器一到立刻能建学院）
        if (countBuildingBuilt(info, BUILDING_STABLE) >= 1 && info.Wood >= 180)
            ensureBuild(BUILDING_COLLAGE);

        // 后勤将兵营单位人口占用减半，先研究再继续扩军。
        // 不再依赖探路成功（探路成功率仅 20%，等探路成功会让科技永远不研发）；
        // 改为研发时预留侦察兵 100 食（scoutFoodReserve），食物够才研发，不抢侦察兵命根子。
        if (countBuildingBuilt(info, BUILDING_ARMYCAMP) >= 1) {
            researchTech(BUILDING_ARMYCAMP, BUILDING_ARMYCAMP_RESEARCH_LOGISTICS,
                         BUILDING_ARMYCAMP_RESEARCH_LOGISTICS_FOOD + scoutFoodReserve(info), 0, 0,
                         BUILDING_ARMYCAMP_RESEARCH_LOGISTICS_GOLD,
                         g_watchLogistics, g_logisticsResearched);
        }

        // 车轮科技（市场，解锁战车弓）：木耗远程主力，不受岛上金矿限制（150食100木）。
        // 去掉 g_siegeKnown 依赖（同上），研发时预留侦察兵 100 食
        if (countBuildingBuilt(info, BUILDING_MARKET) >= 1) {
            researchTech(BUILDING_MARKET, BUILDING_MARKET_WHEEL_UPGRADE, 150 + scoutFoodReserve(info), 100, 0, 0,
                         g_watchWheel, g_wheelResearched);
        }

        // 复合弓科技（靶场，解锁复合弓）：精锐远程，20金/个受金矿限制（180食100木）。
        // 去掉 g_siegeKnown 依赖（同上），研发时预留侦察兵 100 食
        if (countBuildingBuilt(info, BUILDING_RANGE) >= 1) {
            researchTech(BUILDING_RANGE, BUILDING_RANGE_UPGRADE_COMPOSITE_BOW, 180 + scoutFoodReserve(info), 100, 0, 0,
                         g_watchComposite, g_compositeResearched);
        }
    }
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
        if (b.Type == BUILDING_SIEGE) {
            dr = (b.BlockDR + 0.5) * BLOCK; ur = (b.BlockUR + 0.5) * BLOCK;
            return true;
        }
    return false;
}

// 训练 + 防守 + 反攻
// ==================== 侦察兵探路与训练（独立函数） ====================
// 抽成独立函数的原因：这段原先内联在 controlMilitary 里，而块内有多个 return；
// 一旦侦察兵卡住，每帧都会 return 并**整段跳过 controlMilitary 后续的产兵与进攻指挥**，
// 等于整个军事 AI 停摆（实测 map1 只撑到 18000 帧就被灭，连第三波都没到）。
// 独立成函数后，return 只退出本函数，不影响后面的训练/进攻逻辑。
void UsrAI::controlScout(const tagInfo& info)
{
    const double BLOCK = double(BLOCKSIDELENGTH);
    // [日志探针] 每 600 帧采样侦察兵位置 → 事后检测"卡死"(位置长时间不变)与探路进度
    {
        static int s_lastScoutSample = -100000;
        if (g_scoutSN >= 0 && info.GameFrame - s_lastScoutSample >= 600) {
            s_lastScoutSample = info.GameFrame;
            for (const auto& a : info.armies)
                if (a.SN == g_scoutSN) {
                    qInfo() << "[STAT] scout_pos frame" << info.GameFrame
                            << "dr" << int(a.DR / BLOCK) << "ur" << int(a.UR / BLOCK)
                            << "state" << int(a.NowState)
                            << "lastOrder" << (info.GameFrame - g_scoutLastOrderFrame)
                            << "phase" << g_scoutPhase << "known" << (g_siegeKnown ? 1 : 0);
                    break;
                }
        }
    }
    // ===== 侦察探路：第二波后（13500 帧）即派侦察兵 =====
    // 上轮 22000 帧太晚，探路成功全落在 18 分钟后，反攻窗口几乎错过。
    // 提前到 13500 帧（第二波后）侦察；但升铜器前训侦察兵会耗 100 食拖慢升铜，故
    // 加食物保护：工具时代需食物攒到 900（800 升铜 + 100 侦察）才训，铜器后随时训。
    if (!g_siegeKnown && info.GameFrame > 13500) {
        // 探路时机：第三波发起后给部队留足到达/交战时间（最慢投石车 80 秒≈2000 帧），
        // 且视野内敌兵已少（被清或回撤）才出发；26000 帧兜底（再等就错过反攻窗口）
        int visibleEnemies = 0;
        for (const auto& e : info.enemy_armies) if (e.Blood > 0) visibleEnemies++;
        const bool scoutReadyToPath = (info.GameFrame > 23000 && visibleEnemies < 4)
                                   || info.GameFrame > 26000;
        // 已有侦察兵存活检测（死了重训）
        if (g_scoutSN >= 0) {
            bool alive = false;
            for (const auto& a : info.armies) if (a.SN == g_scoutSN) { alive = true; break; }
            if (!alive) {
                // [日志探针] 侦察兵阵亡 → 探路中断/失败的原因之一
                qInfo() << "[STAT] scout_died frame" << info.GameFrame;
                g_scoutSN = -1;
            }
        }
        // 找现存侦察兵（含刚训练完新分配的 SN）
        int scoutSN = -1;
        for (const auto& a : info.armies) if (a.Sort == AT_SCOUT) { scoutSN = a.SN; break; }
        if (scoutSN < 0 && g_scoutSN < 0) {
            // 无侦察兵 → 马厩训一个（100 食，不占黄金；实际成本 config=100，勿改回 60）
            // 升铜后才训：工具时代专注升铜器（800 食优先），铜器后食物自然攒到 100 即训，
            // 避免"工具时代攒 900 食训侦察兵"拖慢升铜（上轮实测升铜被推到 23.6 分钟）
            bool canAffordScout = info.civilizationStage >= CIVILIZATION_BRONZEAGE
                && info.Meat >= 100;
            for (const auto& b : info.buildings) {
                if (b.Type != BUILDING_STABLE || b.Percent < 100 || b.Project != ACT_NULL) continue;
                if (g_assigned.count(b.SN)) continue;
                if (canAffordScout) {
                    BuildingAction(b.SN, BUILDING_STABLE_CREATE_SCOUT);
                    g_assigned.insert(b.SN);
                    break;   // 下一帧找新分配的 SN
                }
            }
        } else {
            if (scoutSN >= 0 && scoutSN != g_scoutSN) {
                // 侦察兵重训（旧兵阵亡）：重置探路状态，从阶段0重新走 L 形。
                // 否则新兵会沿用旧兵的阶段（如 ph=2），从市中心直线穿海卡死。
                g_scoutSN = scoutSN;
                g_scoutTrainFrame = info.GameFrame;   // 记录训出时刻（scoutFoodReserve 熔断计时起点）
                g_scoutPhase = 0;
                g_scoutNoProgressFrame = 0;
                g_scoutNoProgressBX = -1;
                g_scoutNoProgressBY = -1;
                g_scoutPath.clear();
                g_scoutLastOrderFrame = info.GameFrame;
            } else if (scoutSN >= 0) {
                g_scoutSN = scoutSN;
            }
            // 探到厂区则记录真实坐标（siege_found 由上方统计块统一打点，含坐标）
            if (enemySiegePos(info, g_siegeKnownDR, g_siegeKnownUR)) {
                g_siegeKnown = true;
            } else if (scoutReadyToPath) {
                // [日志探针] 探路开始（第一次真正出发）
                static int s_scoutPathLogged = 0;
                if (!s_scoutPathLogged) {
                    s_scoutPathLogged = 1;
                    qInfo() << "[STAT] scout_path_start frame" << info.GameFrame;
                }
                // 探路时机已到（第三波后 + 地图清净）：走 L 形陆路推进探路
                const tagArmy* scout = nullptr;
                for (const auto& a : info.armies) if (a.SN == g_scoutSN) { scout = &a; break; }
                if (scout && scout->NowState == HUMAN_STATE_IDLE
                    && info.GameFrame - g_scoutLastOrderFrame > 45) {
                    // L 形陆路分段推进：4方向BFS确认地图中部有斜向海带，"朝镜像点"直线必穿海；
                    // 唯一可靠陆路是 L 形（先沿 UR=20 行横走，再沿 DR=86 列竖走，终点右下角）。
                    // 每段≤7格：侦察兵视野8，目标点必须落在已探索区（isWalkable 拒绝未探索块，
                    // 超出视野的目标会永远找不到可行走格而卡死）。防抖45帧（7格约62帧走完）。
                    int cb = (int)(scout->DR / BLOCK), cu = (int)(scout->UR / BLOCK);
                    // 方案F2（无进展超时强制换相）：以"前进锚点块"为基准，侦察兵块位置
                    // 曼哈顿距离>=3 即刷新锚点+时间戳；长时间净位移<3格说明在极小区域打转
                    // （摆动/死胡同/海锚点），强制换相脱困。独立于任何会被归零的计数。
                    if (g_scoutNoProgressBX < 0) {
                        g_scoutNoProgressBX = cb; g_scoutNoProgressBY = cu;
                        g_scoutNoProgressFrame = info.GameFrame;
                    } else if (std::abs(cb - g_scoutNoProgressBX) + std::abs(cu - g_scoutNoProgressBY) >= 3) {
                        g_scoutNoProgressBX = cb; g_scoutNoProgressBY = cu;
                        g_scoutNoProgressFrame = info.GameFrame;
                    } else if (info.GameFrame - g_scoutNoProgressFrame > 1200) {
                        g_scoutPhase++;
                        g_scoutNoProgressBX = cb; g_scoutNoProgressBY = cu;
                        g_scoutNoProgressFrame = info.GameFrame;
                        g_scoutLastOrderFrame = info.GameFrame;
                        return;
                    }
                    /* 旧逻辑：硬编码 L 形路点（map.njust 专属坐标），随机到 map1/map2 会撞斜向海带卡死。
                    if (cb < 4 || cu < 4) { g_scoutPhase = 0; gx = 22*BLOCK; gy = 20*BLOCK; }
                    else if (g_scoutPhase <= 1) { gx = 78*BLOCK; gy = 16*BLOCK; if (cb >= 74) g_scoutPhase = 2; }
                    else { gx = 78*BLOCK; gy = 86*BLOCK; if (cu >= 82) g_scoutPhase = 1; }
                    */
                    // 新逻辑（方案C）：把「市中心→镜像点」这条对角线**延伸到地图边界**作为目标。
                    // 为什么不是走到镜像点就停：实测三图镜像点离真实厂区还有 11~18 格
                    // （map 镜像(77,79) vs 厂区(86,86)），超过侦察兵视野 8 格 → 停在镜像点等于白走。
                    // 而沿该方向延伸到边界后，厂区几乎就落在这条线上（垂距 map 1.8 格 / map1 0.5 格），
                    // 走过去必然扫进视野。四个阶段轮流用不同的延伸方向，保证覆盖。
                    double gx, gy;   // 当前锚点（格中心像素坐标）
                    {
                        int cdr = MAP_L / 2, cur = MAP_U / 2;
                        centerBlockPos(info, cdr, cur);   // 取市中心；取不到则用地图中心兜底
                        // 四个候选延伸方向（dx,dy）：镜像对角线及其三个旋转变体
                        int mdx = (MAP_L - 1 - cdr) - cdr;   // 镜像方向 X 分量
                        int mdy = (MAP_U - 1 - cur) - cur;   // 镜像方向 Y 分量
                        int dx = mdx, dy = mdy;
                        switch (g_scoutPhase & 3) {
                        case 0:  dx = mdx;  dy = mdy;  break;   // 主对角线（最可能命中厂区）
                        case 1:  dx = mdx;  dy = -mdy; break;   // 副对角线
                        case 2:  dx = mdx;  dy = 0;    break;   // 水平延伸
                        default: dx = 0;    dy = mdy;  break;   // 垂直延伸
                        }
                        // 从市中心沿 (dx,dy) 延伸到地图边界（内缩 2 格防越界）
                        const int LO = 2, HI_DR = MAP_L - 1 - 2, HI_UR = MAP_U - 1 - 2;
                        double tDR = (dx > 0) ? double(HI_DR - cdr) / dx
                                   : (dx < 0 ? double(LO - cdr) / dx : 1e18);
                        double tUR = (dy > 0) ? double(HI_UR - cur) / dy
                                   : (dy < 0 ? double(LO - cur) / dy : 1e18);
                        double t = std::min(tDR, tUR);
                        if (t > 1e17) t = 0;
                        int eDR = cdr + int(dx * t), eUR = cur + int(dy * t);
                        gx = (eDR + 0.5) * BLOCK;
                        gy = (eUR + 0.5) * BLOCK;
                    }
                    double dx = gx - scout->DR, dy = gy - scout->UR;
                    double dl = std::sqrt(dx * dx + dy * dy);
                    // 抵达当前锚点（2 格内）仍未发现厂区 → 换下一个锚点继续扫
                    if (dl <= 2 * BLOCK) {
                        g_scoutPhase++;
                        g_scoutNoProgressBX = -1;   // 换相后重置前进锚点，重新计时
                        g_scoutNoProgressBY = -1;
                        g_scoutLastOrderFrame = info.GameFrame;
                        return;
                    }
                    double step = std::min(dl, 7.0 * BLOCK);   // 每段最多 7 格（视野内）
                    int tb = (int)((scout->DR + dx / dl * step) / BLOCK);
                    int tu = (int)((scout->UR + dy / dl * step) / BLOCK);
                    if (tb == cb && tu == cu) { g_scoutLastOrderFrame = info.GameFrame; return; }
                    // 目标块避障：与障碍物（海/树/建筑）保持 2 格间隔，走得更顺不易卡拐角。
                    // 两级螺旋均选"离理想点最近"的候选（防漂向反方向）；找不到再放宽为可走。
                    int bi = tb, bj = tu;
                    bool idealOk = isWalkable(info, tb, tu) && obstacleClear(info, tb, tu, 2);
                    if (!idealOk) {
                        bool found = false;
                        for (int r = 1; r <= 8 && !found; r++) {
                            int bestI = -1, bestJ = -1; double bestD = 1e18;
                            for (int i = tb - r; i <= tb + r; i++) {
                                for (int j = tu - r; j <= tu + r; j++) {
                                    if (abs(i - tb) != r && abs(j - tu) != r) continue;
                                    // 必须排除侦察兵当前所在块：前方被海带堵死时，(cb,cu) 落在螺旋半径内
                                    // 且可走，会被当成"最近可走点"选中 → HumanMove 到自己脚下 → 原地踏步
                                    // 永久卡死（实测 map 卡在 (33,23) 直到游戏结束）。
                                    if (i == cb && j == cu) continue;
                                    if (!isWalkable(info, i, j) || !obstacleClear(info, i, j, 2)) continue;
                                    double dd = (i - tb) * (i - tb) + (j - tu) * (j - tu);
                                    if (dd < bestD) { bestD = dd; bestI = i; bestJ = j; }
                                }
                            }
                            if (bestI >= 0) { bi = bestI; bj = bestJ; found = true; }
                        }
                        if (!found) {   // 放宽：只要求可走
                            for (int r = 1; r <= 8 && !found; r++) {
                                int bestI = -1, bestJ = -1; double bestD = 1e18;
                                for (int i = tb - r; i <= tb + r; i++) {
                                    for (int j = tu - r; j <= tu + r; j++) {
                                        if (abs(i - tb) != r && abs(j - tu) != r) continue;
                                        if (i == cb && j == cu) continue;   // 同上：排除原地
                                        if (!isWalkable(info, i, j)) continue;
                                        double dd = (i - tb) * (i - tb) + (j - tu) * (j - tu);
                                        if (dd < bestD) { bestD = dd; bestI = i; bestJ = j; }
                                    }
                                }
                                if (bestI >= 0) { bi = bestI; bj = bestJ; found = true; }
                            }
                            if (!found) {
                                /* 旧逻辑：两级螺旋都失败就直接 return —— 这正是卡死的根源。
                                   两级螺旋都以「前方目标块 (tb,tu)」为中心搜索；侦察兵正面撞上大片
                                   斜向海带时，(tb,tu) 及其 8 格内全是海，两级都失败 → 每帧 return，
                                   侦察兵原地空转、位置永不变（实测 map1 卡在 (57,48) 整整 30 分钟）。
                                if (!found) { g_scoutLastOrderFrame = info.GameFrame; return; }
                                */
                                // 新逻辑：沿海绕行。以「侦察兵自身位置 (cb,cu)」为中心，在周围可走块里
                                // 选「朝目标方向投影最大」的一个——等价于贴着海带边缘朝目标滑行绕开障碍。
                                // 自身位置必然可走，故只要身周还有陆地就不会卡死；四周全海才放弃本帧。
                                double ux = dx / dl, uy = dy / dl;   // 目标方向单位向量
                                int bestI = -1, bestJ = -1; double bestProj = -1e18;
                                for (int r = 1; r <= 5 && bestI < 0; r++) {
                                    for (int i = cb - r; i <= cb + r; i++) {
                                        for (int j = cu - r; j <= cu + r; j++) {
                                            if (i == cb && j == cu) continue;     // 排除当前所在块
                                            if (!isWalkable(info, i, j)) continue;
                                            double proj = (i - cb) * ux + (j - cu) * uy;
                                            if (proj > bestProj) { bestProj = proj; bestI = i; bestJ = j; }
                                        }
                                    }
                                }
                                if (bestI < 0) { g_scoutLastOrderFrame = info.GameFrame; return; }
                                bi = bestI; bj = bestJ;
                            }
                        }
                    }
                    /* 旧兜底：目标块等于当前块就 return。实测反而更容易卡死——
                       排除"当前块"后可选点变少，侦察兵常常无点可走而彻底停摆。
                    if (bi == cb && bj == cu) { g_scoutLastOrderFrame = info.GameFrame; return; }
                    */
                    // 可达性检查：改用 4 连通 BFS（与引擎寻路一致），不再用「直线采样」——
                    // 直线采样会把「BFS 连通但需绕弯」的路径误判为不可达，导致反复下令却原地不动（卡死/打转）。
                    auto bfsReach = [&](int sr, int sc, int tr, int tc) -> bool {
                        if (sr == tr && sc == tc) return true;
                        if (!isWalkable(info, tr, tc)) return false;
                        const int W = MAP_L, H = MAP_U;
                        std::vector<char> seen(W * H, 0);
                        std::vector<std::pair<int,int>> q; q.reserve(256);
                        auto id = [&](int x, int y){ return y * W + x; };
                        q.push_back({sr, sc}); seen[id(sr,sc)] = 1;
                        const int d4x[4] = {1,-1,0,0}, d4y[4] = {0,0,1,-1};
                        int head = 0;
                        while (head < (int)q.size()) {
                            int x = q[head].first, y = q[head].second; head++;
                            for (int k = 0; k < 4; k++) {
                                int nx = x + d4x[k], ny = y + d4y[k];
                                if (nx < 0 || ny < 0 || nx >= W || ny >= H) continue;
                                if (seen[id(nx,ny)]) continue;
                                if (!isWalkable(info, nx, ny)) continue;
                                if (nx == tr && ny == tc) return true;
                                seen[id(nx,ny)] = 1;
                                q.push_back({nx, ny});
                            }
                        }
                        return false;
                    };
                    // 终极兜底：所有方向都不可达时，BFS 找「可达集内离目标最近」的点并走过去。
                    // 只要身周还有陆地就不会冻结；自然沿海带绕行，也不会左右小步打转。
                    auto bfsBestStep = [&](int sr, int sc, int tr, int tc, int maxR) -> std::pair<int,int> {
                        const int W = MAP_L, H = MAP_U;
                        std::vector<int> dist(W * H, -1);
                        auto id = [&](int x, int y){ return y * W + x; };
                        std::vector<std::pair<int,int>> q; q.reserve(256);
                        q.push_back({sr, sc}); dist[id(sr,sc)] = 0;
                        const int d4x[4] = {1,-1,0,0}, d4y[4] = {0,0,1,-1};
                        int head = 0, bestX = sr, bestY = sc;
                        int bestD = std::abs(sr - tr) + std::abs(sc - tc);
                        while (head < (int)q.size()) {
                            int x = q[head].first, y = q[head].second; head++;
                            int d = std::abs(x - tr) + std::abs(y - tc);
                            if (d < bestD) { bestD = d; bestX = x; bestY = y; }
                            if (dist[id(x,y)] >= maxR) continue;
                            for (int k = 0; k < 4; k++) {
                                int nx = x + d4x[k], ny = y + d4y[k];
                                if (nx < 0 || ny < 0 || nx >= W || ny >= H) continue;
                                if (dist[id(nx,ny)] != -1) continue;
                                if (!isWalkable(info, nx, ny)) continue;
                                dist[id(nx,ny)] = dist[id(x,y)] + 1;
                                q.push_back({nx, ny});
                            }
                        }
                        return {bestX, bestY};
                    };
                    // BFS 贪心作为主寻路：在「从当前块可达」的格子集合里，挑离锚点(gx,gy)最近的一个走过去。
                    // 这保证每一步都朝锚点单调推进（不会来回/打转），遇海自动沿海绕行，且永不冻结。
                    // 锚点若被海带隔断不可达，BFS 会把侦察兵带到「可达范围内离锚点最近」的点；
                    // 若连续多帧无法再靠近，则切换下一个锚点(phase++)避免卡死。
                    auto bfsBestToward = [&](int sr, int sc, double gx, double gy, int maxR)
                            -> std::pair<int,int> {
                        const int W = MAP_L, H = MAP_U;
                        std::vector<int> dist(W * H, -1);
                        auto id = [&](int x, int y){ return y * W + x; };
                        std::vector<std::pair<int,int>> q; q.reserve(256);
                        q.push_back({sr, sc}); dist[id(sr,sc)] = 0;
                        const int d4x[4] = {1,-1,0,0}, d4y[4] = {0,0,1,-1};
                        int head = 0;
                        int bestX = sr, bestY = sc;
                        double bestD = calDistance((sr + 0.5) * BLOCK, (sc + 0.5) * BLOCK, gx, gy);
                        while (head < (int)q.size()) {
                            int x = q[head].first, y = q[head].second; head++;
                            if (dist[id(x,y)] >= maxR) continue;
                            for (int k = 0; k < 4; k++) {
                                int nx = x + d4x[k], ny = y + d4y[k];
                                if (nx < 0 || ny < 0 || nx >= W || ny >= H) continue;
                                if (dist[id(nx,ny)] != -1) continue;
                                if (!isWalkable(info, nx, ny)) continue;
                                dist[id(nx,ny)] = dist[id(x,y)] + 1;
                                double dd = calDistance((nx + 0.5) * BLOCK, (ny + 0.5) * BLOCK, gx, gy);
                                if (dd < bestD - 1e-6) { bestD = dd; bestX = nx; bestY = ny; }
                                q.push_back({nx, ny});
                            }
                        }
                        return {bestX, bestY};
                    };
                    // 方案1（2026-08-31）+ 方案A（2026-09-01）：沿海绕行。
                    // bfsBestToward 在 7 格 BFS 内找不到更接近锚点的可达点（前方被宽海带
                    // 隔断，或锚点本身落在海里不可达）时，全 5 层扫描 + 综合评分
                    // "投影最大 - 0.5×绕远惩罚" 沿海滑动绕行。换相不再靠 micro/slide/stall
                    // （会归零/过敏），改由上方"无进展超时"（g_scoutNoProgressFrame）统一判定。
                    {
                        auto best = bfsBestToward(cb, cu, gx, gy, 7);
                        if (best.first == cb && best.second == cu) {
                            double ux = dx / dl, uy = dy / dl;   // 目标方向单位向量
                            double curD = calDistance((cb + 0.5) * BLOCK, (cu + 0.5) * BLOCK, gx, gy);
                            int slideI = -1, slideJ = -1; double bestScore = -1e18;
                            for (int r = 1; r <= 5; r++) {
                                for (int i = cb - r; i <= cb + r; i++) {
                                    for (int j = cu - r; j <= cu + r; j++) {
                                        if (i == cb && j == cu) continue;     // 排除当前所在块
                                        if (!isWalkable(info, i, j)) continue;
                                        double proj = (i - cb) * ux + (j - cu) * uy;
                                        double candD = calDistance((i + 0.5) * BLOCK, (j + 0.5) * BLOCK, gx, gy);
                                        double extra = candD - curD; if (extra < 0) extra = 0;
                                        double score = proj - 0.5 * extra;   // 投影优先、绕远受罚
                                        if (score > bestScore) { bestScore = score; slideI = i; slideJ = j; }
                                    }
                                }
                            }
                            if (slideI >= 0) {
                                bi = slideI; bj = slideJ;
                            } else {
                                // 四周全海/无可走块（理论极少），本帧不动，等无进展超时换相
                                g_scoutLastOrderFrame = info.GameFrame;
                                return;
                            }
                        } else {
                            bi = best.first; bj = best.second;
                        }
                    }
                    HumanMove(g_scoutSN, (bi + 0.5) * BLOCK, (bj + 0.5) * BLOCK);
                    if (g_scoutPath.empty() || g_scoutPath.back() != std::make_pair(bi, bj))
                        g_scoutPath.push_back({bi, bj});
                    g_scoutLastOrderFrame = info.GameFrame;
                    // （诊断日志 scout_go 已清理）
                }
            } else {
                // 待命：探路时机未到（第三波未过/地图仍有敌兵）→ 回市中心附近待命，
                // 不出去送死。第三波来袭时它在家，由箭塔+军队连带保护。
                const tagArmy* scout = nullptr;
                for (const auto& a : info.armies) if (a.SN == g_scoutSN) { scout = &a; break; }
                if (scout && info.GameFrame - g_scoutLastOrderFrame > 45) {
                    int cdr = 0, cur = 0;
                    if (centerBlockPos(info, cdr, cur)) {
                        double hx = (cdr + 0.5) * BLOCK, hy = (cur + 0.5) * BLOCK;
                        if (calDistance(scout->DR, scout->UR, hx, hy) > 2 * BLOCK) {
                            HumanMove(g_scoutSN, hx, hy);
                            g_scoutLastOrderFrame = info.GameFrame;
                        }
                    }
                }
            }
        }
    }
}

void UsrAI::controlMilitary(const tagInfo& info)
{
    const double BLOCK = double(BLOCKSIDELENGTH);

    controlScout(info);

    // 冲铜器阶段：前置已建好且食物接近门槛 → 暂停训练，全力攒 800 食升铜器。
    // 阈值 700（与 readyUpgrade 一致，非 500）：避免前置一建成就停训防守兵，导致工具时代防守真空。
    bool prepareUpgrade = false;
    if (info.civilizationStage == CIVILIZATION_TOOLAGE && info.Meat >= 700) {
        int tb = (countBuildingBuilt(info, BUILDING_MARKET) > 0)
               + (countBuildingBuilt(info, BUILDING_RANGE) > 0)
               + (countBuildingBuilt(info, BUILDING_STABLE) > 0);
        prepareUpgrade = (tb >= 2);
    }

    // 兵力生产策略：工具时代折中少量防守兵（投石远程防早期rush + 棍棒肉盾，保护农民不被打崩）；
    // 铜器后大幅提高兵员生产（远程为主近战为辅，持续不断补到满编）。
    const int armyCap = (info.civilizationStage >= CIVILIZATION_BRONZEAGE)
        ? (g_underAttack ? 30 : 26)
        : (g_underAttack ? 8 : 5);
    int queuedUnits = 0;
    auto canTrain = [&]() {
        return countArmy(info) + queuedUnits < armyCap
            && info.Human_Num + queuedUnits < info.Human_MaxNum - 3;
    };
    // 产兵食物门槛：铜器后未探路时额外预留 100 食给侦察兵，避免产兵把侦察兵饿死
    const int scoutReserve = scoutFoodReserve(info);
    auto meatFor = [&](int cost) { return info.Meat >= cost + scoutReserve; };

    // 规则1：第三波已到但仍在工具时代 → "先升铜再产兵"，暂停一切训练，食物让给升铜器
    const bool forbidTrain = isWave3RushBronze(info);

    if (!prepareUpgrade && !forbidTrain) {
    // 兵营训练（工具时代：只训少量棍棒近战刀斧兵；铜器：远程为主近战为辅）
    for (const auto& b : info.buildings) {
        if (b.Type != BUILDING_ARMYCAMP || b.Percent < 100 || b.Project != ACT_NULL) continue;
        if (g_assigned.count(b.SN)) continue;
        if (!canTrain()) continue;
        if (info.civilizationStage == CIVILIZATION_TOOLAGE && info.GameFrame > 2500) {
            // 工具时代折中防守：投石兵（远程，40食10石）优先打早期rush的棍棒/骑兵；其次棍棒（50食）肉盾
            if (meatFor(40) && info.Stone >= 10) {
                BuildingAction(b.SN, BUILDING_ARMYCAMP_CREATE_SLINGER);
                g_assigned.insert(b.SN);
                queuedUnits++;
                continue;
            }
            if (meatFor(50)) {
                BuildingAction(b.SN, BUILDING_ARMYCAMP_CREATE_CLUBMAN);
                g_assigned.insert(b.SN);
                queuedUnits++;
                continue;
            }
        } else if (info.civilizationStage >= CIVILIZATION_BRONZEAGE) {
            // 铜器：兵营只训棍棒（近战肉盾），远程交给靶场的高级弓兵（战车弓/复合弓）
            if (meatFor(50)) {
                BuildingAction(b.SN, BUILDING_ARMYCAMP_CREATE_CLUBMAN);
                g_assigned.insert(b.SN);
                queuedUnits++;
                continue;
            }
        }
    }

    // 靶场训练：工具时代训普通弓；铜器训战车弓（40食70木，需车轮科技，远程主力）
    for (const auto& b : info.buildings) {
        if (b.Type != BUILDING_RANGE || b.Percent < 100 || b.Project != ACT_NULL) continue;
        if (g_assigned.count(b.SN)) continue;
        if (!canTrain()) continue;
        if (info.civilizationStage >= CIVILIZATION_BRONZEAGE) {
            // 高级弓优先（复合弓精锐/战车弓主力），资源不足降级训普通弓（40食20木），保证远程不断档
            if (g_compositeResearched && meatFor(40) && info.Gold >= 20) {
                BuildingAction(b.SN, BUILDING_RANGE_CREATE_COMPOSITE_BOWMAN);
                g_assigned.insert(b.SN);
                queuedUnits++;
            } else if (g_wheelResearched && meatFor(40) && info.Wood >= 70) {
                BuildingAction(b.SN, BUILDING_RANGE_CREATE_CHARIOT_ARCHER);
                g_assigned.insert(b.SN);
                queuedUnits++;
            } else if (meatFor(40) && info.Wood >= 20) {
                BuildingAction(b.SN, BUILDING_RANGE_CREATE_BOWMAN);
                g_assigned.insert(b.SN);
                queuedUnits++;
            }
        } else if (meatFor(40) && info.Wood >= 20) {
            BuildingAction(b.SN, BUILDING_RANGE_CREATE_BOWMAN);
            g_assigned.insert(b.SN);
            queuedUnits++;
        }
    }

    // ===== 铜器时代高级兵 =====
    if (info.civilizationStage >= CIVILIZATION_BRONZEAGE) {
        // 学院：方阵兵（60食40金，肉盾）优先于骑兵——黄金稀缺，方阵兵性价比更高
        for (const auto& b : info.buildings) {
            if (b.Type != BUILDING_COLLAGE || b.Percent < 100 || b.Project != ACT_NULL) continue;
            if (g_assigned.count(b.SN)) continue;
            if (!canTrain()) continue;
            if (meatFor(60) && info.Gold >= 40) {
                BuildingAction(b.SN, BUILDING_COLLAGE_CREATE_HOPLITE);
                g_assigned.insert(b.SN);
                queuedUnits++;
            }
        }
        // 马厩：骑兵（70食80金）——仅在黄金充足(>200，留 40 金余量给方阵兵)时才造
        for (const auto& b : info.buildings) {
            if (b.Type != BUILDING_STABLE || b.Percent < 100 || b.Project != ACT_NULL) continue;
            if (g_assigned.count(b.SN)) continue;
            if (!canTrain()) continue;
            // 骑兵（70食80金）：门槛=80实际成本+40方阵余量=120（勿再写200，开局150金永远造不出）
            if (meatFor(70) && info.Gold >= 120) {
                BuildingAction(b.SN, BUILDING_STABLE_CREATE_CAVALRY);
                g_assigned.insert(b.SN);
                queuedUnits++;
            }
        }
    }
    }   // end if(!prepareUpgrade)：冲铜器阶段不训练，但仍执行下方防守/反攻

    // ===== 防守 / 反攻 =====
    // 反攻时机：攒够 12 兵就总攻（后期加快推进），26000 帧超时兜底
    bool offense = (info.GameFrame > 21000 && countArmy(info) >= 12)
                || info.GameFrame > 26000;
    double targetDR = 0, targetUR = 0;
    bool hasTarget = false;
    if (offense) {
        // 进攻目标优先：已探明的厂区真实坐标 → 实时 enemySiegePos → 镜像兜底
        if (g_siegeKnown) {
            targetDR = g_siegeKnownDR; targetUR = g_siegeKnownUR; hasTarget = true;
        } else if (enemySiegePos(info, targetDR, targetUR)) {
            g_siegeKnown = true; g_siegeKnownDR = targetDR; g_siegeKnownUR = targetUR; hasTarget = true;
        } else {
            double sx = 0, sy = 0; int n = 0;
            for (const auto& b : info.enemy_buildings) {
                sx += (b.BlockDR + 0.5) * BLOCK; sy += (b.BlockUR + 0.5) * BLOCK; n++;
            }
            if (n > 0) { targetDR = sx / n; targetUR = sy / n; hasTarget = true; }
            else {
                int cdr = 0, cur = 0;
                if (centerBlockPos(info, cdr, cur)) {
                    targetDR = (MAP_L - 1 - cdr + 0.5) * BLOCK;
                    targetUR = (MAP_U - 1 - cur + 0.5) * BLOCK;
                    hasTarget = true;
                }
            }
        }
    }

    // 厂区 25 格内敌方单位数（清场完成判定依据；无厂区坐标时视为未清场）
    int enemiesNearSiege = -1;
    if (hasTarget) {
        enemiesNearSiege = 0;
        for (const auto& e : info.enemy_armies)
            if (e.Blood > 0 && calDistance(e.DR, e.UR, targetDR, targetUR) <= 25 * BLOCK) enemiesNearSiege++;
        for (const auto& f : info.enemy_farmers)
            if (f.Blood > 0 && calDistance(f.DR, f.UR, targetDR, targetUR) <= 25 * BLOCK) enemiesNearSiege++;
    }
    // 军队重心（判断是否已推进到厂区附近，避免"没到厂区就误判清场完成"）
    double armyDR = 0, armyUR = 0;
    bool hasArmy = armyCenterPos(info, armyDR, armyUR);
    bool armyAtSiege = hasTarget && hasArmy
        && calDistance(armyDR, armyUR, targetDR, targetUR) <= 20 * BLOCK;
    // 清场完成：军队已到厂区附近 且 厂区 25 格内无敌军
    bool cleared = armyAtSiege && enemiesNearSiege == 0;

    // 士兵移动辅助：避障（目标块不可走则螺旋找最近可走块）+ 防抖（距上次下令<60帧不重发）
    auto moveArmyTo = [&](int sn, double goalDR, double goalUR) {
        if (g_armyLastOrderFrame.count(sn) && info.GameFrame - g_armyLastOrderFrame[sn] < 60) return;
        int tb = (int)(goalDR / BLOCK), tu = (int)(goalUR / BLOCK);
        int bi = tb, bj = tu;
        if (!isWalkable(info, tb, tu)) {
            bool found = false;
            for (int r = 1; r <= 12 && !found; r++) {
                for (int i = tb - r; i <= tb + r && !found; i++) {
                    for (int j = tu - r; j <= tu + r && !found; j++) {
                        if (abs(i - tb) != r && abs(j - tu) != r) continue;
                        if (isWalkable(info, i, j)) { bi = i; bj = j; found = true; }
                    }
                }
            }
            if (!found) return;   // 附近无可行走格，放弃本帧
        }
        HumanMove(sn, (bi + 0.5) * BLOCK, (bj + 0.5) * BLOCK);
        g_armyLastOrderFrame[sn] = info.GameFrame;
    };

    // 散开站位：以 (gx,gy) 为中心、半径 3~8 格的环形偏移点（按 SN 散列，防士兵挤成一团互相卡位）
    auto scatterPoint = [&](int sn, double gx, double gy) -> std::pair<double, double> {
        // 士兵围绕目标点轻微散开（半径 2~3.6 格，稍微聚集不挤一堆，也不散太开）
        int slot = sn % 10;
        double ang = slot * (2 * 3.14159265358979 / 10.0);
        double r = (2.0 + (sn % 3) * 0.8) * BLOCK;
        return std::make_pair(gx + std::cos(ang) * r, gy + std::sin(ang) * r);
    };

    // 祭司受袭检测：谁正在攻击祭司（祭司死亡=战败，优先保护）
    int priestSN = findPriestSN(info);
    int priestAttacker = -1;
    double attackerDR = 0, attackerUR = 0;
    bool priestUnderAttack = false;
    if (priestSN >= 0) {
        priestAttacker = findAttackerSN(info, priestSN);
        if (priestAttacker >= 0 && enemyDetailPos(info, priestAttacker, attackerDR, attackerUR))
            priestUnderAttack = true;
    }

    static long long g_throwerMoveTotal = 0;   // 诊断：投石车移动指令累计（擦边改动后应接近0，验证来回消除）
    // 投石车 SN -> 上次下发"贴身退避"的帧。用 SN 级而非单个 static，避免多辆投石车共用一份冷却而互相卡住。
    static std::map<int, int> g_throwerRetreatFrame;
    // [日志探针] 总攻期每 300 帧采样一次阵型：远程/近战到最近敌的距离。
    // 事后用于检测"是否冲进敌堆"——远程最小距离过小(=贴脸)即说明没保持自身攻击距离。
    {
        static int s_lastSampleFrame = -100000;
        if (offense && info.GameFrame - s_lastSampleFrame >= 300) {
            s_lastSampleFrame = info.GameFrame;
            int rc = 0, mc = 0; double rmin = 1e18, rsum = 0, mmin = 1e18, msum = 0;
            for (const auto& a : info.armies) {
                if (a.Sort == AT_PRIEST || a.Sort == AT_SCOUT) continue;
                double nd2 = 1e18;
                int en2 = nearestEnemySN(info, a.DR, a.UR, nd2);
                if (en2 < 0) continue;
                if (isRangedUnit(a.Sort)) { rc++; rsum += nd2; if (nd2 < rmin) rmin = nd2; }
                else                      { mc++; msum += nd2; if (nd2 < mmin) mmin = nd2; }
            }
            qInfo() << "[STAT] formation frame" << info.GameFrame
                    << "ranged_n" << rc << "ranged_min" << (rc ? int(rmin / BLOCK) : -1)
                    << "ranged_avg" << (rc ? int(rsum / rc / BLOCK) : -1)
                    << "melee_n" << mc << "melee_min" << (mc ? int(mmin / BLOCK) : -1)
                    << "melee_avg" << (mc ? int(msum / mc / BLOCK) : -1)
                    << "thrower_moves" << g_throwerMoveTotal;
        }
    }

    for (const auto& a : info.armies) {
        if (a.Sort == AT_PRIEST) continue;   // 祭司由 controlPriest 处理
        if (a.Sort == AT_SCOUT) continue;    // 侦察兵由上方探路逻辑控制，不参与防守/反攻（否则命令冲突原地打转）
        const bool ranged = isRangedUnit(a.Sort);
        // 远程兵处于攻击中(ATTACKING)也要持续评估 kite 距离（修贴脸 FAIL）；
        // 近战兵及其它状态仅空闲时接受指令，避免打断走位/攻击。
        if (a.NowState != HUMAN_STATE_IDLE && !(ranged && a.NowState == HUMAN_STATE_ATTACKING))
            continue;

        // 祭司受袭：15 格内的空闲士兵优先转火攻击者（远处士兵不调回，保住防线）
        if (a.NowState == HUMAN_STATE_IDLE && priestUnderAttack
            && calDistance(a.DR, a.UR, attackerDR, attackerUR) <= 15 * BLOCK) {
            HumanAction(a.SN, priestAttacker);
            continue;
        }

        if (offense) {
            double nd = 1e18;
            int enemy = nearestEnemySN(info, a.DR, a.UR, nd);
            // 攻城武器厂只能由祭司转化取胜，士兵严禁攻击（否则打掉厂区=永远无法转化获胜）
            if (enemy >= 0 && isSiegeBuildingSN(info, enemy)) enemy = -1;
            // 取消"严禁攻击投石车"（它会站在箭塔火力外白拆家），但祭司正在转化的那一台
            // 要避让，让祭司抢到转化——否则军队先打死，祭司永远转化不到。
            if (enemy >= 0 && enemy == g_priestConvertTargetSN) enemy = -1;
            // bool ranged 已在循环开头声明

            // 远程兵：保持自身攻击距离 —— 最近敌 <8 格(贴脸)先 kite 到 12 格再射，
            // 绝不站在敌堆里原地对射（用户要求：就近打 + 各自保持自身攻击距离 + 不进敌堆）。
            if (ranged) {
                double kx = 0, ky = 0; double ndK = 1e18;
                int nk = nearestEnemySN(info, a.DR, a.UR, ndK);
                if (nk >= 0 && enemyDetailPos(info, nk, kx, ky)) {
                    if (a.Sort == AT_STONE_THROWER) {
                        // 我方投石车：擦边攻击，卸掉来回反复前进后退。射程 [2,10] 格（config.json:
                        // DIS_MIN_STONE_THROWER=2 / DIS_STONE_THROWER=10）。射程内站定只攻击不移动；
                        // 仅被近战贴身(<4格)退到射程边缘(10格)一次到位，下一帧即在射程内站定，不反复大退。
                        if (ndK < 4 * BLOCK) {
                            // 退避防抖（2026-08-31 加）：近战兵速度 2.439 > 投石车 1.626，投石车一退就被
                            // 追上，ndK 持续 <4 格 → 若无防抖则每帧重发 moveArmyTo，指令数虚高
                            // (map1 run4 实测 156 次)，观感仍像来回拉扯且反复重置寻路。
                            // 改法：上一条退避还在执行(移动中)且距上次下发 <60 帧 → 不重发，让引擎走完这段。
                            // 站定(IDLE)时被贴身仍立即退避，不影响保命。
                            auto itRet = g_throwerRetreatFrame.find(a.SN);
                            const bool inRetreatCd = (itRet != g_throwerRetreatFrame.end())
                                                  && (info.GameFrame - itRet->second < 60);
                            if (a.NowState == HUMAN_STATE_WALKING && inRetreatCd) {
                                continue;   // 正在执行上一次退避，本帧不重发指令（也不攻击）
                            }
                            double rx = a.DR - kx, ry = a.UR - ky;   // 背敌方向
                            double rl = std::sqrt(rx * rx + ry * ry);
                            double sx = a.DR, sy = a.UR;
                            if (rl > 1) { sx = a.DR + rx / rl * 10 * BLOCK; sy = a.UR + ry / rl * 10 * BLOCK; }
                            sx = fmax(BLOCK, fmin(sx, (MAP_L - 1) * BLOCK));
                            sy = fmax(BLOCK, fmin(sy, (MAP_U - 1) * BLOCK));
                            auto sp = scatterPoint(a.SN, sx, sy);
                            moveArmyTo(a.SN, sp.first, sp.second);
                            g_throwerRetreatFrame[a.SN] = info.GameFrame;   // 记帧，供上方防抖判冷却
                            g_throwerMoveTotal++;
                            continue;   // 本帧仅退到射程边缘，不攻击
                        }
                        // 射程内(>=4格)或射程外：不在此拦截，落下方 enemy 分支（射程内攻击 / 射程外推进）
                    } else if (ndK < 8 * BLOCK) {
                        double rx = a.DR - kx, ry = a.UR - ky;   // 背敌方向
                        double rl = std::sqrt(rx * rx + ry * ry);
                        double sx = a.DR, sy = a.UR;
                        if (rl > 1) { sx = a.DR + rx / rl * 12 * BLOCK; sy = a.UR + ry / rl * 12 * BLOCK; }
                        sx = fmax(BLOCK, fmin(sx, (MAP_L - 1) * BLOCK));
                        sy = fmax(BLOCK, fmin(sy, (MAP_U - 1) * BLOCK));
                        auto sp = scatterPoint(a.SN, sx, sy);
                        moveArmyTo(a.SN, sp.first, sp.second);
                        continue;   // 本帧先拉开距离，不攻击
                    }
                }
            }

            if (enemy >= 0) {
                // 远程兵：仅空闲时发起攻击，攻击中靠引擎持续输出（不每帧重置攻击动作，这正是贴脸 FAIL 的前置条件）；
                // 近战兵：空闲或敌人贴近(<=8格)时反击。
                bool canAttack = ranged ? (a.NowState == HUMAN_STATE_IDLE)
                                        : (a.NowState == HUMAN_STATE_IDLE || nd <= 8 * BLOCK);
                if (canAttack && (ranged || cleared || nd <= 8 * BLOCK)) {
                    HumanAction(a.SN, enemy);
                }
                // 近战兵在敌人较远时：不追击，继续向厂区外圈集结位推进（下方移动分支）
            }
            if (enemy < 0 || (!ranged && !cleared && nd > 8 * BLOCK)) {
                // 远程兵无敌人时向厂区推进；近战兵未清场时推进到厂区外 18 格集结（不深入集火圈）
                if (hasTarget) {
                    if (ranged) {
                        // 远程兵安全线：停在厂区外 20 格——在近战(15~18格)集结位**之后**，
                        // 形成"近战前排 / 远程后排"的分批，绝不推进到厂区=敌堆。
                        // 18~22 格区间内原地待命（保持自身攻击距离），不来回蹭。
                        double dx = a.DR - targetDR, dy = a.UR - targetUR;
                        double dist = std::sqrt(dx * dx + dy * dy);
                        if (dist < 1) { dx = 1; dy = 0; dist = 1; }
                        if (dist < 18 * BLOCK || dist > 22 * BLOCK) {
                            auto sp = scatterPoint(a.SN,
                                targetDR + dx / dist * 20 * BLOCK,
                                targetUR + dy / dist * 20 * BLOCK);
                            moveArmyTo(a.SN, sp.first, sp.second);
                        }
                    } else {
                        // 近战兵集结位：厂区外 18 格（沿当前→厂区方向取 18 格处），散开站位
                        double dx = a.DR - targetDR, dy = a.UR - targetUR;
                        double dist = std::sqrt(dx * dx + dy * dy);
                        if (dist > 20 * BLOCK) {
                            auto sp = scatterPoint(a.SN, targetDR, targetUR);
                            moveArmyTo(a.SN, sp.first, sp.second);   // 太远，先向厂区推进
                        } else if (dist < 15 * BLOCK) {
                            auto sp = scatterPoint(a.SN,
                                targetDR + dx / dist * 18 * BLOCK,
                                targetUR + dy / dist * 18 * BLOCK);
                            moveArmyTo(a.SN, sp.first, sp.second); // 太近，退回 18 格
                        }
                        // 15~20 格区间：原地待命，等远程兵清场
                    }
                }
            }
        } else {
            // ===== 防守目标选择（规则2 + 规则3） =====
            // 规则2：优先打"已进入我方箭塔 7 格射程"的敌人 —— 我方一旦出手，敌方
            //        FindWaveTargetByPriority 会把仇恨转到"正在打它的对象"，敌人便停在塔下，
            //        由箭塔持续输出（箭塔自动索敌开火，无需指令）。塔内无敌则正常打最近敌人。
            // 取消"严禁攻击投石车"：投石车射程 10 格 > 箭塔 7 格，站在塔火力外白拆市镇中心，
            // 实测导致升铜变慢、祭司第三波后大量阵亡，故恢复军队正常攻击。
            // 但要给祭司"锁定权"：祭司正在转化的那一台（g_priestConvertTargetSN）军队避让，
            // 否则军队会在祭司读条完成前先把目标打死，祭司就永远转化不到。
            int towerTarget = -1; double towerDist = 1e18;   // 箭塔射程内的敌人（规则2 优先）
            int nearTarget  = -1; double nearDist  = 1e18;   // 最近敌人（兜底，正常打）
            auto considerTarget = [&](int sn, double dr, double ur, int sort, bool isFarmer) {
                if (isSiegeBuildingSN(info, sn)) return;             // 攻城武器厂留给祭司转化
                if (sn == g_priestConvertTargetSN) return;       // 让给祭司转化，别抢人头
                double d = calDistance(a.DR, a.UR, dr, ur);
                if (isInTowerRange(info, dr, ur) && d < towerDist) { towerDist = d; towerTarget = sn; }
                if (d < nearDist) { nearDist = d; nearTarget = sn; }
            };
            for (const auto& e : info.enemy_armies)
                if (e.Blood > 0) considerTarget(e.SN, e.DR, e.UR, e.Sort, false);
            for (const auto& f : info.enemy_farmers)
                if (f.Blood > 0) considerTarget(f.SN, f.DR, f.UR, -1, true);

            // 塔内敌人优先，但绝不舍近求远：若塔内目标比最近目标远 2 倍以上、且超过 20 格，
            // 仍打最近的那个（否则会放着身边正在打祭司的敌人不管，跑去追塔下远处的目标）。
            int enemy = nearTarget;
            if (towerTarget >= 0
                && (towerDist <= nearDist * 2.0 || towerDist <= 20 * BLOCK))
                enemy = towerTarget;
            if (enemy >= 0 && a.NowState == HUMAN_STATE_IDLE) {
                HumanAction(a.SN, enemy);
            } else {
                // 防守待命：围绕市中心散开站位（按 SN 环形偏移），不全部挤在市中心一点
                int bdr = 0, bur = 0;
                if (centerBlockPos(info, bdr, bur)) {
                    auto sp = scatterPoint(a.SN, (bdr + 0.5) * BLOCK, (bur + 0.5) * BLOCK);
                    if (calDistance(a.DR, a.UR, sp.first, sp.second) > 3 * BLOCK)
                        moveArmyTo(a.SN, sp.first, sp.second);
                }
            }
        }
    }
}

// ==================== 村民反击 ====================
// 敌军来袭检测(15格) + 反击调度（最近5个空闲村民 + 被敌人锁定的空闲村民）+ 解除后恢复
// 方案2：原任务由 g_farmerTargetSN 跨帧保留，解除后自动回归原目标，身份不切换
void UsrAI::controlFarmerDefense(const tagInfo& info)
{
    const double BLOCK = double(BLOCKSIDELENGTH);
    const double ALERT_RANGE = 15 * BLOCK;   // 触发半径：敌人进入市镇中心 15 格
    const double CLEAR_RANGE = 20 * BLOCK;   // 解除半径：敌人全灭或退到 20 格外（迟滞防抖动）

    // 新逻辑（用户方案）：升铜资源交付前村民不反击——第一波（2斧+1弓）由祭司转化+箭塔处理，
    // 村民全程采集食物冲升铜（反击=放弃采集+村民死亡=经济崩盘）。
    {
        bool bronzeCommitted = false;
        if (info.civilizationStage >= CIVILIZATION_BRONZEAGE) bronzeCommitted = true;
        for (const auto& b : info.buildings)
            if (b.Type == BUILDING_CENTER && b.Project == BUILDING_CENTER_UPGRADE)
                bronzeCommitted = true;
        if (!bronzeCommitted) return;
    }

    // 市镇中心坐标
    double cdx = 0, cdy = 0;
    bool hasCenter = false;
    for (const auto& b : info.buildings)
        if (b.Type == BUILDING_CENTER) {
            cdx = (b.BlockDR + 0.5) * BLOCK; cdy = (b.BlockUR + 0.5) * BLOCK; hasCenter = true; break;
        }

    // 最近存活敌军（军队）距市镇中心的距离
    double minDist = 1e18;
    for (const auto& a : info.enemy_armies) {
        if (a.Blood <= 0) continue;
        double d = hasCenter ? calDistance(cdx, cdy, a.DR, a.UR) : 0.0;
        if (hasCenter && d < minDist) minDist = d;
    }

    // 状态切换（迟滞防抖动）
    if (g_underAttack) {
        if (minDist >= CLEAR_RANGE) {
            g_underAttack = false;
            // 恢复阶段：清理死亡村民的残留状态（期间有人死了就刷新）
            for (auto it = g_farmerTargetSN.begin(); it != g_farmerTargetSN.end();) {
                bool alive = false;
                for (const auto& f : info.farmers) if (f.SN == it->first) { alive = true; break; }
                if (!alive) it = g_farmerTargetSN.erase(it);
                else ++it;
            }
        }
    } else {
        if (minDist <= ALERT_RANGE)
            g_underAttack = true;
    }

    if (!g_underAttack) return;   // 无战斗，正常经济

    // ===== 战斗期：选反击名单（最近 5 个空闲村民 + 被敌人锁定的空闲村民） =====
    // 1) 被敌人锁定（正在被打）的对象 SN
    std::set<int> targeted;
    for (const auto& a : info.enemy_armies)
        if (a.WorkObjectSN >= 0) targeted.insert(a.WorkObjectSN);
    for (const auto& e : info.enemy_farmers)
        if (e.WorkObjectSN >= 0) targeted.insert(e.WorkObjectSN);

    // 2) 空闲村民按「到最近敌人的距离」升序
    std::vector<std::pair<double,int>> idleList;
    for (const auto& f : info.farmers) {
        if (f.FarmerSort != FARMERTYPE_FARMER || f.NowState != HUMAN_STATE_IDLE) continue;
        if (g_assigned.count(f.SN)) continue;
        double nd = 1e18;
        int enemySN = nearestEnemyUnitSN(info, f.DR, f.UR, nd);
        if (enemySN >= 0) idleList.push_back(std::make_pair(nd, f.SN));
    }
    std::sort(idleList.begin(), idleList.end());

    // 3) 反击名单：最近 5 个 + 被敌人锁定的空闲村民
    std::set<int> defenders;
    for (size_t i = 0; i < idleList.size() && i < 5; i++)
        defenders.insert(idleList[i].second);
    for (const auto& f : info.farmers) {
        if (f.FarmerSort != FARMERTYPE_FARMER || f.NowState != HUMAN_STATE_IDLE) continue;
        if (g_assigned.count(f.SN)) continue;
        if (targeted.count(f.SN)) defenders.insert(f.SN);
    }

    // 4) 反击：每个反击村民攻击最近的敌人（其余空闲村民留给 economy 正常采集）
    for (const auto& f : info.farmers) {
        if (f.FarmerSort != FARMERTYPE_FARMER || f.NowState != HUMAN_STATE_IDLE) continue;
        if (g_assigned.count(f.SN)) continue;
        if (!defenders.count(f.SN)) continue;
        double nd = 1e18;
        int enemy = nearestEnemyUnitSN(info, f.DR, f.UR, nd);
        if (enemy >= 0) {
            HumanAction(f.SN, enemy);
            g_assigned.insert(f.SN);
        }
    }
}

// ==================== 箭塔指挥（User 层索敌下令） ====================
// 引擎自动索敌（manageMontorAct）因建筑未注册视野而失效，箭塔是哑炮。
// 但引擎在指令分派处给箭塔开了特例：HumanAction(箭塔SN, 敌人SN) 会走 handleMilitaryAction
// 建立攻击关系（Core.cpp SORT_BUILDING→BUILDING_ARROWTOWER 分支）。故在 User 层手动点名：
// 每座已建成箭塔找射程内最近敌人下令；防抖 45 帧（同目标不重发，避免 respond=true 的
// addRelation 每帧 suspend 打断攻击——这正是引擎自动索敌失效的同类机制）。
void UsrAI::controlTowers(const tagInfo& info)
{
    const double BLOCK = double(BLOCKSIDELENGTH);
    const double TOWER_RANGE = 7 * BLOCK;   // DIS_ARROWTOWER = 7 格
    const int    COOLDOWN = 45;             // 防抖帧（≈1.8 秒，攻击动画远短于此）

    for (const auto& b : info.buildings) {
        if (b.Type != BUILDING_ARROWTOWER || b.Percent < 100) continue;

        // 射程内最近敌人：优先军队，其次敌方农民（不主动打敌方建筑，留给军队/祭司）
        double bx = (b.BlockDR + 0.5) * BLOCK, by = (b.BlockUR + 0.5) * BLOCK;
        int bestSN = -1; double bestD = 1e18;
        for (const auto& e : info.enemy_armies) {
            if (e.Blood <= 0) continue;
            double d = calDistance(bx, by, e.DR, e.UR);
            if (d <= TOWER_RANGE && d < bestD) { bestD = d; bestSN = e.SN; }
        }
        if (bestSN < 0) {
            for (const auto& f : info.enemy_farmers) {
                if (f.Blood <= 0) continue;
                double d = calDistance(bx, by, f.DR, f.UR);
                if (d <= TOWER_RANGE && d < bestD) { bestD = d; bestSN = f.SN; }
            }
        }

        auto it = g_towerCmd.find(b.SN);
        if (bestSN < 0) {
            if (it != g_towerCmd.end()) g_towerCmd.erase(it);   // 射程内无敌人：清记录，空闲待机
            continue;
        }
        // 同目标且冷却未到 → 不重发（不打断正在执行的攻击）
        if (it != g_towerCmd.end() && it->second.first == bestSN
            && info.GameFrame - it->second.second < COOLDOWN) continue;

        HumanAction(b.SN, bestSN);
        g_towerCmd[b.SN] = std::make_pair(bestSN, info.GameFrame);
    }
}

// ==================== 卡住检测（农民 240 帧无变化 → 挪动换活） ====================
void UsrAI::detectStuck(const tagInfo& info)
{
    const double BLOCK = double(BLOCKSIDELENGTH);
    for (const auto& f : info.farmers) {
        if (f.FarmerSort != FARMERTYPE_FARMER) continue;
        if (g_assigned.count(f.SN)) continue;              // 本帧刚派活，跳过
        if (f.NowState == HUMAN_STATE_WORKING) continue;   // 正在干活（种田/施工/采矿）位置不动是正常的，不判卡住
        if (f.NowState == HUMAN_STATE_ATTACKING) continue; // 反击中的村民不判卡住（远程目标打不到时位置可能长期不变）
        if (g_stuckCooldown.count(f.SN) && info.GameFrame < g_stuckCooldown[f.SN]) continue;

        bool changed = false;
        if (g_stuckFrame.count(f.SN)) {
            double pd = g_stuckDR.count(f.SN) ? g_stuckDR[f.SN] : -1e9;
            double pu = g_stuckUR.count(f.SN) ? g_stuckUR[f.SN] : -1e9;
            if (fabs(f.DR - pd) > 1.0 || fabs(f.UR - pu) > 1.0) changed = true;
            if (g_stuckState.count(f.SN) && g_stuckState[f.SN] != f.NowState) changed = true;
            if (g_stuckRes.count(f.SN) && g_stuckRes[f.SN] != f.Resource) changed = true;
        }

        if (changed) {
            g_stuckFrame[f.SN] = 0;
            g_stuckDR[f.SN] = f.DR; g_stuckUR[f.SN] = f.UR;
            g_stuckState[f.SN] = f.NowState;
            g_stuckRes[f.SN] = f.Resource;
        } else {
            g_stuckFrame[f.SN]++;
            // 连续无变化 → 挪动换活（IDLE村民120帧/5秒，其他240帧/10秒）
            int stuckThreshold = (f.NowState == HUMAN_STATE_IDLE) ? 120 : 240;
            if (g_stuckFrame[f.SN] >= stuckThreshold) {
                int bdr = 0, bur = 0;
                if (centerBlockPos(info, bdr, bur)) {
                    HumanMove(f.SN, (bdr + 1.5) * BLOCK, (bur + 1.5) * BLOCK);
                    g_stuckCooldown[f.SN] = info.GameFrame + 600;   // 10 秒冷却，防反复打断
                }
                g_stuckFrame[f.SN] = 0;
                g_stuckDR[f.SN] = f.DR; g_stuckUR[f.SN] = f.UR;
                g_stuckState[f.SN] = f.NowState;
                g_stuckRes[f.SN] = f.Resource;
            } else {
                g_stuckDR[f.SN] = f.DR; g_stuckUR[f.SN] = f.UR;
                g_stuckState[f.SN] = f.NowState;
                g_stuckRes[f.SN] = f.Resource;
            }
        }
    }
}
