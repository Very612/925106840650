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

static std::set<int> g_assigned;
static std::set<int> g_buildAssigned;
static std::set<int> g_farmAssigned;
static int g_jobRound = 0;
static std::map<int,int> g_farmerTargetSN;
static std::map<int,int> g_buildDispatch;
static bool g_swordResearched = false;
static bool g_meleeResearched = false;
static bool g_towerUpgradeResearched = false;
static bool g_logisticsResearched = false;
static bool g_wheelResearched = false;
static bool g_compositeResearched = false;
static bool g_woodUpgradeResearched = false;

struct TechWatch { bool researching = false; int frame = -100000; };
static TechWatch g_watchComposite, g_watchWheel, g_watchLogistics;
static bool g_underAttack = false;

static std::map<int,int> g_farmerFarm;
static std::set<int>     g_ownedFarms;

static const int FOOD_ALERT_THRESHOLD = 120;
static void pruneFarmLeases(const tagInfo& info);

static const int WAVE3_FRAME = 21000;

static const int ARROWTOWER_RANGE_BLOCKS = 7;

static const int THROWER_WAVE3_MIN_DIST_FROM_SIEGE = 25;

static const int THROWER_WAVE3_MAX_DIST_FROM_CENTER = 45;

static bool isWave3RushBronze(const tagInfo& info);
static bool isInTowerRange(const tagInfo& info, double dr, double ur);
static bool isWave3StoneThrower(const tagInfo& info, const tagArmy& thrower);

static int g_lastBuildDR = -1, g_lastBuildUR = -1, g_lastBuildSize = -1;
static std::set<std::pair<int,int>> g_frameBuildPos;
static int g_buildSeq = 0;

static std::map<int, int>    g_stuckFrame;
static std::map<int, double> g_stuckDR, g_stuckUR;
static std::map<int, int>    g_stuckState, g_stuckRes;
static std::map<int, int>    g_stuckCooldown;

static int g_towerPhase = 0;
static int g_towerWaitFrame = 0;
static int g_towerStartFrame = 0;

enum PriestMoveMode { PRIEST_MOVE_NONE = 0, PRIEST_MOVE_RETREAT, PRIEST_MOVE_FOLLOW, PRIEST_MOVE_OBJECTIVE };
static int    g_priestMoveMode = PRIEST_MOVE_NONE;
static double g_priestMoveDR = 0, g_priestMoveUR = 0;
static int    g_priestMoveFrame = -100000;
static int    g_priestRetreatUntil = -100000;
static double g_priestRetreatTX = -1, g_priestRetreatTY = -1;
static int    g_priestRetreatCommit = -100000;

static int    g_priestConvertTargetSN = -1;

enum OffensePhase { OFFENSE_NONE = 0, OFFENSE_SCOUT, OFFENSE_CLEAR, OFFENSE_CONVERT };
static int g_offensePhase = OFFENSE_NONE;
static double g_siegeKnownDR = 0, g_siegeKnownUR = 0;
static bool   g_siegeKnown = false;
static int    g_scoutSN = -1;
static int    g_scoutTrainFrame = -1;
static int    g_scoutLastOrderFrame = -100000;

static int    g_scoutPhase = 0;

static int    g_scoutNoProgressFrame = 0;
static int    g_scoutNoProgressBX = -1;
static int    g_scoutNoProgressBY = -1;
static std::vector<std::pair<int,int>> g_scoutPath;
static std::map<int,int> g_armyLastOrderFrame;
static std::map<int,std::pair<int,int>> g_towerCmd;

static bool isRangedUnit(int sort)
{
    return sort == AT_SLINGER || sort == AT_BOWMAN || sort == AT_IMPROVED
        || sort == AT_COMPOSITE_BOWMAN || sort == AT_CHARIOT_ARCHER
        || sort == AT_STONE_THROWER;
}

static bool isSiegeBuildingSN(const tagInfo& info, int sn)
{
    for (const auto& b : info.enemy_buildings)
        if (b.SN == sn && b.Type == BUILDING_SIEGE && b.Blood > 0) return true;
    return false;
}

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
    default:                return 30;
    }
}

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
    g_frameBuildPos.clear();

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
    }
    g_lastGameFrame = info.GameFrame;
    g_assigned.clear();
    g_buildAssigned.clear();
    g_farmAssigned.clear();
    pruneFarmLeases(info);
    controlBuilding(info);
    controlFarmerDefense(info);
    controlEconomy(info);
    controlMilitary(info);
    controlTowers(info);
    controlPriest(info);
    detectStuck(info);

}

int UsrAI::findPriestSN(const tagInfo& info)
{
    for (const auto& a : info.armies)
        if (a.Sort == AT_PRIEST) return a.SN;
    return -1;
}

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

int UsrAI::findAttackerSN(const tagInfo& info, int priestSN)
{
    for (const auto& a : info.enemy_armies)  if (a.Blood > 0 && a.WorkObjectSN == priestSN) return a.SN;
    for (const auto& f : info.enemy_farmers) if (f.Blood > 0 && f.WorkObjectSN == priestSN) return f.SN;
    return -1;
}

int UsrAI::findWoundedAllySN(const tagInfo& info, int priestSN)
{
    (void)priestSN;
    int best = -1; double br = 1e18;
    auto consider = [&](int sn, int blood, int maxblood) {
        if (maxblood <= 0 || blood >= maxblood) return;
        double ratio = double(blood) / double(maxblood);
        if (ratio < br) { br = ratio; best = sn; }
    };
    for (const auto& a : info.armies)
        if (a.SN != priestSN) consider(a.SN, a.Blood, a.MaxBlood);
    for (const auto& f : info.farmers) consider(f.SN, f.Blood, f.MaxBlood);
    return best;
}

bool UsrAI::centerBlockPos(const tagInfo& info, int& bdr, int& bur)
{
    for (const auto& b : info.buildings)
        if (b.Type == BUILDING_CENTER) { bdr = b.BlockDR; bur = b.BlockUR; return true; }
    return false;
}

void UsrAI::controlPriest(const tagInfo& info)
{
    const double BLOCK = double(BLOCKSIDELENGTH);
    const double CONVERT_RANGE = double(DIS_PRIEST) * BLOCK;

    int priestSN = findPriestSN(info);
    if (priestSN < 0) { g_priestConvertTargetSN = -1; return; }
    const tagArmy* priest = nullptr;
    for (const auto& a : info.armies) if (a.SN == priestSN) { priest = &a; break; }
    if (!priest) { g_priestConvertTargetSN = -1; return; }

    if (g_priestConvertTargetSN >= 0) {
        bool targetAlive = false;
        for (const auto& a : info.enemy_armies)
            if (a.SN == g_priestConvertTargetSN && a.Blood > 0) { targetAlive = true; break; }
        if (!targetAlive) g_priestConvertTargetSN = -1;
    }

    bool offense = (info.GameFrame > 21000 && countArmy(info) >= 12)
                || info.GameFrame > 26000;

    auto issueMove = [&](int mode, double dr, double ur, double stopDistance) -> bool {

        const int prevMode = g_priestMoveMode;
        if (calDistance(priest->DR, priest->UR, dr, ur) <= stopDistance) return false;

        if (priest->NowState == HUMAN_STATE_WALKING) {
            if (calDistance(g_priestMoveDR, g_priestMoveUR, dr, ur) <= 2 * BLOCK) return false;
            if (info.GameFrame - g_priestMoveFrame < 45) return false;
        }
        HumanMove(priestSN, dr, ur);
        g_priestMoveMode = mode;
        g_priestMoveDR = dr;
        g_priestMoveUR = ur;
        g_priestMoveFrame = info.GameFrame;

        if (mode == PRIEST_MOVE_RETREAT) {
            const bool newRetreat = (prevMode != PRIEST_MOVE_RETREAT)
                                 || (info.GameFrame >= g_priestRetreatUntil);
            if (newRetreat) g_priestRetreatUntil = info.GameFrame + 90;
        }
        return true;
    };
    auto retreatToSafe = [&]() -> bool {

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

        if (hasTower) {
            int tb = (int)(tdr / BLOCK), tu = (int)(tur / BLOCK);
            bool edgeBad = (tb < 5 || tu < 5 || tb >= MAP_L - 5 || tu >= MAP_U - 5);
            bool farFromCenter = false;
            int cdr0 = 0, cur0 = 0;
            if (centerBlockPos(info, cdr0, cur0))
                farFromCenter = (std::abs(tb - cdr0) + std::abs(tu - cur0) > 12);
            if (edgeBad || farFromCenter) hasTower = false;
        }
        double nd = 1e18;
        int ne = nearestEnemyUnitSN(info, priest->DR, priest->UR, nd);
        if (ne >= 0) {

            if (nd > 18 * BLOCK) return false;

            if (hasTower) {
                double ex = 0, ey = 0;
                if (ne >= 0 && enemyDetailPos(info, ne, ex, ey)) {
                    double vx = tdr - ex, vy = tur - ey;
                    double vl = std::sqrt(vx * vx + vy * vy);
                    if (vl > 0.01) {
                        const double R = 3.5 * BLOCK;
                        const double base = std::atan2(vy, vx);
                        const double OFF[5] = { 0.0, 0.6, -0.6, 1.2, -1.2 };
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

                return issueMove(PRIEST_MOVE_RETREAT, tdr, tur, 2 * BLOCK);
            }
            double ed = 0, eu = 0;
            bool hasEnemy = enemyDetailPos(info, ne, ed, eu);

            double adr = 0, aur = 0;
            bool hasArmy = armyCenterPos(info, adr, aur);

            double fx = 0, fy = 0;
            bool hasFlee = false;
            if (hasEnemy) {
                double dx = priest->DR - ed, dy = priest->UR - eu;
                double dl = std::sqrt(dx * dx + dy * dy);
                if (dl < 1) { dx = 1; dy = 0; dl = 1; }
                fx = priest->DR + dx / dl * 15 * BLOCK;
                fy = priest->UR + dy / dl * 15 * BLOCK;

                if (fx < 5 * BLOCK) fx = 5 * BLOCK;
                if (fy < 5 * BLOCK) fy = 5 * BLOCK;
                if (fx > (MAP_L - 5) * BLOCK) fx = (MAP_L - 5) * BLOCK;
                if (fy > (MAP_U - 5) * BLOCK) fy = (MAP_U - 5) * BLOCK;
                hasFlee = true;
            }

            double rx = 0, ry = 0; bool hasRear = false;
            if (hasTower) { rx = tdr; ry = tur; hasRear = true; }
            else { int bdr = 0, bur = 0; if (centerBlockPos(info, bdr, bur)) { rx = (bdr + 0.5) * BLOCK; ry = (bur + 0.5) * BLOCK; hasRear = true; } }

            if (info.GameFrame > g_priestRetreatCommit || g_priestRetreatTX < 0) {
                double tx = -1, ty = -1;

                if (hasRear)                      { tx = rx;  ty = ry; }
                else if (hasFlee)                 { tx = fx;  ty = fy; }
                else if (hasArmy)                 { tx = adr; ty = aur; }
                if (tx >= 0) { g_priestRetreatTX = tx; g_priestRetreatTY = ty; g_priestRetreatCommit = info.GameFrame + 150; }
            }
            if (g_priestRetreatTX >= 0)
                return issueMove(PRIEST_MOVE_RETREAT, g_priestRetreatTX, g_priestRetreatTY, 2 * BLOCK);

            if (hasArmy) return issueMove(PRIEST_MOVE_RETREAT, adr, aur, 3 * BLOCK);
            if (hasFlee) return issueMove(PRIEST_MOVE_RETREAT, fx, fy, 2 * BLOCK);
        }

        if (hasTower)
            return issueMove(PRIEST_MOVE_RETREAT, tdr, tur, 2 * BLOCK);
        double adr = 0, aur = 0;
        if (armyCenterPos(info, adr, aur))
            return issueMove(PRIEST_MOVE_FOLLOW, adr, aur, 3 * BLOCK);
        int bdr = 0, bur = 0;
        if (!centerBlockPos(info, bdr, bur)) return false;
        return issueMove(PRIEST_MOVE_RETREAT, (bdr + 0.5) * BLOCK, (bur + 0.5) * BLOCK, 2 * BLOCK);
    };

    bool hasEnemyUnit = false;
    bool hasCombatUnit = false;
    for (const auto& a : info.enemy_armies) if (a.Blood > 0) { hasEnemyUnit = true; hasCombatUnit = true; break; }
    if (!hasEnemyUnit)
        for (const auto& f : info.enemy_farmers) if (f.Blood > 0) { hasEnemyUnit = true; break; }

    bool towerThreat = false;
    for (const auto& b : info.enemy_buildings) {
        if (b.Type == BUILDING_ARROWTOWER && b.Blood > 0) {
            double bdr = (b.BlockDR + 0.5) * BLOCK, bur = (b.BlockUR + 0.5) * BLOCK;
            if (calDistance(priest->DR, priest->UR, bdr, bur) <= 7 * BLOCK) {
                towerThreat = true; break;
            }
        }
    }

    const int bloodThreshold = offense ? 60 : 40;
    if (priest->Blood < bloodThreshold) { retreatToSafe(); return; }

    {
        int throwerAttacker = findAttackerSN(info, priestSN);
        if (throwerAttacker >= 0) {
            for (const auto& e : info.enemy_armies)
                if (e.SN == throwerAttacker && e.Sort == AT_STONE_THROWER) { retreatToSafe(); return; }
        }
    }

    if (priest->NowState == HUMAN_STATE_ATTACKING) return;

    if (hasCombatUnit) {
        if (priest->ConvertCooldown > 0) {

            if (offense) {
                int atk = findAttackerSN(info, priestSN);
                if (atk >= 0) retreatToSafe();
                return;
            }
            retreatToSafe();
            return;
        }

        int target = -1;
        double tdr = 0, tur = 0;
        int attacker = findAttackerSN(info, priestSN);
        if (attacker >= 0 && enemyDetailPos(info, attacker, tdr, tur)) {
            target = attacker;
        } else {

            auto guardCount = [&](double dr, double ur) -> int {
                int c = 0;
                for (const auto& e : info.enemy_armies)
                    if (e.Blood > 0 && calDistance(e.DR, e.UR, dr, ur) <= 6 * BLOCK) c++;
                return c;
            };
            const int GUARD_LIMIT = 3;
            const double REACH_LIMIT = 34 * BLOCK;

            double bv = -1, bd = 1e18; int bestSN = -1;
            for (const auto& a : info.enemy_armies) {
                if (a.Blood <= 0) continue;
                double d = calDistance(priest->DR, priest->UR, a.DR, a.UR);
                if (d > REACH_LIMIT) continue;
                if (guardCount(a.DR, a.UR) >= GUARD_LIMIT) continue;

                int v = (a.Sort == AT_STONE_THROWER && isWave3StoneThrower(info, a))
                        ? 1000 : armyValueScore(a.Sort);
                if (v > bv || (v == bv && d < bd)) { bv = v; bd = d; bestSN = a.SN; }
            }

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
                bestSN = s_lockedSN;
            } else {
                s_lockedSN = bestSN;
                s_lockFrame = info.GameFrame;
            }
            if (bestSN >= 0) {
                target = bestSN;
                enemyDetailPos(info, bestSN, tdr, tur);
            }
        }

        if (target >= 0) {

            g_priestConvertTargetSN = target;
            double d = calDistance(priest->DR, priest->UR, tdr, tur);
            if (d <= CONVERT_RANGE) {

                HumanAction(priestSN, target);
                g_priestMoveMode = PRIEST_MOVE_NONE;
                return;
            }

            double dx = tdr - priest->DR, dy = tur - priest->UR;
            double dl = std::sqrt(dx * dx + dy * dy);
            if (dl < 1) { dx = 1; dy = 0; dl = 1; }
            double k = (d - 11 * BLOCK) / d;
            double gx = fmax(BLOCK, fmin(priest->DR + dx * k, (MAP_L - 1) * BLOCK));
            double gy = fmax(BLOCK, fmin(priest->UR + dy * k, (MAP_U - 1) * BLOCK));

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
                            retreatToSafe();
                            return;
                        }
                    }
                }
            }

            if (info.GameFrame >= g_priestRetreatUntil)
                issueMove(PRIEST_MOVE_FOLLOW, gx, gy, 2 * BLOCK);
            return;
        }
        if (!offense) {

            retreatToSafe();
            return;
        }
    }

    if (towerThreat) { retreatToSafe(); return; }

    if (priest->NowState == HUMAN_STATE_WORKING) return;
    int wounded = findWoundedAllySN(info, priestSN);
    if (wounded >= 0) {
        HumanAction(priestSN, wounded);
        g_priestMoveMode = PRIEST_MOVE_NONE;
        return;
    }

    if (offense) {

        double siegeDR = 0, siegeUR = 0;
        bool siegeKnown = false;
        if (g_siegeKnown) { siegeDR = g_siegeKnownDR; siegeUR = g_siegeKnownUR; siegeKnown = true; }
        else if (enemySiegePos(info, siegeDR, siegeUR)) {
            g_siegeKnown = true; g_siegeKnownDR = siegeDR; g_siegeKnownUR = siegeUR; siegeKnown = true;
        }

        bool cleared = false;
        if (siegeKnown) {
            int nearEnemy = 0;
            for (const auto& e : info.enemy_armies)
                if (e.Blood > 0 && calDistance(e.DR, e.UR, siegeDR, siegeUR) <= 25 * BLOCK) nearEnemy++;

            double armyDR = 0, armyUR = 0;
            bool hasArmy = armyCenterPos(info, armyDR, armyUR);
            bool armyAtSiege = hasArmy && calDistance(armyDR, armyUR, siegeDR, siegeUR) <= 20 * BLOCK;
            cleared = armyAtSiege && nearEnemy <= 3;
        }

        if (siegeKnown && cleared) {

            for (const auto& b : info.enemy_buildings)
                if (b.Type == BUILDING_SIEGE && b.Blood > 0) {
                    HumanAction(priestSN, b.SN);
                    g_priestMoveMode = PRIEST_MOVE_NONE;
                    return;
                }
        } else if (siegeKnown) {

            double armyDR = 0, armyUR = 0;
            if (armyCenterPos(info, armyDR, armyUR)) {
                if (calDistance(armyDR, armyUR, siegeDR, siegeUR) <= 18 * BLOCK) {

                    double ax = armyDR, ay = armyUR;
                    double ex = 0, ey = 0; double ndAnchor = 1e18;
                    int ne = nearestEnemyUnitSN(info, armyDR, armyUR, ndAnchor);

                    if (ne >= 0 && enemyDetailPos(info, ne, ex, ey)) {
                        double rx = armyDR - ex, ry = armyUR - ey;
                        double rl = std::sqrt(rx * rx + ry * ry);
                        if (rl > 1) { ax = armyDR + rx / rl * 5 * BLOCK; ay = armyUR + ry / rl * 5 * BLOCK; }
                    } else {
                        double vx = armyDR - siegeDR, vy = armyUR - siegeUR;
                        double vl = std::sqrt(vx * vx + vy * vy);
                        if (vl > 1) { ax = armyDR + vx / vl * 5 * BLOCK; ay = armyUR + vy / vl * 5 * BLOCK; }
                    }
                    ax = fmax(BLOCK, fmin(ax, (MAP_L - 1) * BLOCK));
                    ay = fmax(BLOCK, fmin(ay, (MAP_U - 1) * BLOCK));
                    issueMove(PRIEST_MOVE_FOLLOW, ax, ay, 3 * BLOCK);
                } else
                    retreatToSafe();
            } else {
                retreatToSafe();
            }
        } else {

            retreatToSafe();
        }
    } else {

        {
            static int patrolIdx = 0;
            static int patrolRing = 0;
            static int patrolLastFrame = -100000;
            if (info.GameFrame - patrolLastFrame > 60) {
                int cdr = 0, cur = 0;
                if (centerBlockPos(info, cdr, cur)) {
                    static const int DX[4] = { 1, 0, -1, 0 };
                    static const int DY[4] = { 0, 1, 0, -1 };
                    const int idx = patrolIdx % 4;
                    int radius = 15 + patrolRing * 5;
                    int txb = cdr + DX[idx] * radius;
                    int tyb = cur + DY[idx] * radius;
                    while (radius > 4 && !isWalkable(info, txb, tyb)) {
                        radius -= 2;
                        txb = cdr + DX[idx] * radius;
                        tyb = cur + DY[idx] * radius;
                    }
                    if (isWalkable(info, txb, tyb)) {
                        double tx = (txb + 0.5) * BLOCK;
                        double ty = (tyb + 0.5) * BLOCK;
                        if (calDistance(priest->DR, priest->UR, tx, ty) <= 2 * BLOCK) {
                            patrolIdx++;
                            if (patrolIdx % 4 == 0 && patrolRing < 3) patrolRing++;
                        } else {
                            HumanMove(priestSN, tx, ty);
                            patrolLastFrame = info.GameFrame;
                        }
                    } else {
                        patrolIdx++;
                    }
                }
            }
        }
    }
}

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

static bool resourceStillValid(const tagInfo& info, int sn)
{
    for (const auto& r : info.resources)
        if (r.SN == sn && (r.Cnt > 0 || r.Blood > 0)) return true;
    for (const auto& b : info.buildings)
        if (b.SN == sn && b.Type == BUILDING_FARM && b.Cnt > 0) return true;
    return false;
}

int UsrAI::countFarmers(const tagInfo& info)
{
    int n = 0;
    for (const auto& f : info.farmers)
        if (f.FarmerSort == FARMERTYPE_FARMER) n++;
    return n;
}

int UsrAI::countBuilding(const tagInfo& info, int type)
{
    int n = 0;
    for (const auto& b : info.buildings)
        if (b.Type == type) n++;
    return n;
}

int UsrAI::countBuildingBuilt(const tagInfo& info, int type)
{
    int n = 0;
    for (const auto& b : info.buildings)
        if (b.Type == type && b.Percent >= 100) n++;
    return n;
}

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

static bool farmHasFarmer(const tagInfo& info, int farmSN, double fdr, double fur)
{
    const double BLOCK = double(BLOCKSIDELENGTH);
    for (const auto& f : info.farmers) {
        if (f.FarmerSort != FARMERTYPE_FARMER) continue;
        if (f.WorkObjectSN == farmSN) return true;
        if (f.NowState == HUMAN_STATE_WORKING) {
            double dx = f.DR - fdr, dy = f.UR - fur;
            if (dx * dx + dy * dy <= 1.5 * 1.5 * BLOCK * BLOCK) return true;
        }
    }
    return false;
}

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

static int countValidFarm(const tagInfo& info)
{
    int n = 0;
    for (const auto& b : info.buildings)
        if (b.Type == BUILDING_FARM && b.Percent >= 100 && b.Cnt > 0) n++;
    return n;
}

int UsrAI::nearestFarmSN(const tagInfo& info, double pr, double pu)
{
    const double BLOCK = double(BLOCKSIDELENGTH);
    int best = -1; double bd = 1e18;
    for (const auto& b : info.buildings) {
        if (b.Type != BUILDING_FARM || b.Percent < 100) continue;
        if (b.Cnt <= 0) continue;
        if (g_farmAssigned.count(b.SN)) continue;
        if (g_ownedFarms.count(b.SN)) continue;
        double fdr = (b.BlockDR + 0.5) * BLOCK, fur = (b.BlockUR + 0.5) * BLOCK;
        if (farmHasFarmer(info, b.SN, fdr, fur)) continue;
        double d = calDistance(pr, pu, fdr, fur);
        if (d < bd) { bd = d; best = b.SN; }
    }
    return best;
}

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

int UsrAI::nearestResourceSN(const tagInfo& info, double pr, double pu, int resClass)
{
    int best = -1; double bd = 1e18;
    for (const auto& r : info.resources) {
        if (!matchResourceClass(r.Type, resClass)) continue;
        if (r.Cnt <= 0 && r.Blood <= 0) continue;
        double d = calDistance(pr, pu, r.DR, r.UR);
        if (d < bd) { bd = d; best = r.SN; }
    }
    return best;
}

static double wave3Dist(double x1, double y1, double x2, double y2)
{
    return pow(pow(x1 - x2, 2) + pow(y1 - y2, 2), 0.5);
}

static bool isWave3RushBronze(const tagInfo& info)
{
    return info.GameFrame >= WAVE3_FRAME
        && info.civilizationStage == CIVILIZATION_TOOLAGE;
}

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

static bool isWave3StoneThrower(const tagInfo& info, const tagArmy& thrower)
{
    const double BLOCK = double(BLOCKSIDELENGTH);

    for (const auto& b : info.enemy_buildings) {
        if (b.Type != BUILDING_SIEGE) continue;
        double sdr = (b.BlockDR + 0.5) * BLOCK;
        double sur = (b.BlockUR + 0.5) * BLOCK;
        double d = wave3Dist(thrower.DR, thrower.UR, sdr, sur);
        return d > double(THROWER_WAVE3_MIN_DIST_FROM_SIEGE) * BLOCK;
    }

    for (const auto& b : info.buildings) {
        if (b.Type != BUILDING_CENTER) continue;
        double cx = (b.BlockDR + 0.5) * BLOCK;
        double cy = (b.BlockUR + 0.5) * BLOCK;
        double d = wave3Dist(thrower.DR, thrower.UR, cx, cy);
        return d < double(THROWER_WAVE3_MAX_DIST_FROM_CENTER) * BLOCK;
    }
    return false;
}

static int scoutFoodReserve(const tagInfo& info)
{

    if (info.civilizationStage < CIVILIZATION_BRONZEAGE) return 0;
    if (g_siegeKnown) return 0;

    if (g_scoutSN >= 0 && g_scoutTrainFrame >= 0
        && info.GameFrame - g_scoutTrainFrame > 6000) return 0;
    return 100;
}

static bool toolBuildingsReady(const tagInfo& info)
{
    int n = 0;
    for (const auto& b : info.buildings)
        if ((b.Type == BUILDING_MARKET || b.Type == BUILDING_RANGE || b.Type == BUILDING_STABLE)
            && b.Percent >= 100)
            n++;
    return n >= 2;
}

int UsrAI::pickResourceClass(const tagInfo& info, int idx)
{
    int r = idx % 10;

    if (info.Meat < FOOD_ALERT_THRESHOLD) {
        if (r < 8) return 0;
        if (r < 9) return 1;
        return 2;
    }
    if (info.civilizationStage >= CIVILIZATION_BRONZEAGE) {

        if (r < 4) return 0;
        if (r < 7) return 3;
        if (r < 9) return 1;
        return 2;
    }

    if (!toolBuildingsReady(info)) {

        if (r < 4) return 0;
        if (r < 9) return 1;
        return 2;
    }

    if (r < 8) return 0;
    if (r < 9) return 1;
    return 2;
}

void UsrAI::controlEconomy(const tagInfo& info)
{
    int farmers = countFarmers(info);

    int target = (info.civilizationStage >= CIVILIZATION_BRONZEAGE) ? 16 : 12;

    bool readyUpgrade = false;
    if (info.civilizationStage == CIVILIZATION_TOOLAGE && info.Meat >= 700) {
        int tb = (countBuildingBuilt(info, BUILDING_MARKET) > 0)
               + (countBuildingBuilt(info, BUILDING_RANGE) > 0)
               + (countBuildingBuilt(info, BUILDING_STABLE) > 0);
        readyUpgrade = (tb >= 2);
    }

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

    for (const auto& f : info.farmers) {
        if (f.FarmerSort != FARMERTYPE_FARMER || f.NowState != HUMAN_STATE_IDLE) continue;
        if (g_assigned.count(f.SN)) continue;
        int sn = -1;

        if (g_farmerTargetSN.count(f.SN) && resourceStillValid(info, g_farmerTargetSN[f.SN])) {
            sn = g_farmerTargetSN[f.SN];
        } else {
            int cls = pickResourceClass(info, g_jobRound++);
            if (cls == 0) {

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
                        g_farmAssigned.insert(sn);
                        g_farmerFarm[f.SN] = sn;
                        g_ownedFarms.insert(sn);
                    } else {
                        sn = nearestResourceSN(info, f.DR, f.UR, 0);
                    }
                }
            } else {
                sn = nearestResourceSN(info, f.DR, f.UR, cls);
            }

            if (sn < 0) {
                for (int fallback = 0; fallback < 4; fallback++) {
                    sn = nearestResourceSN(info, f.DR, f.UR, fallback);
                    if (sn >= 0) break;
                }
                if (sn < 0) sn = nearestFarmSN(info, f.DR, f.UR);
            }
            if (sn >= 0) g_farmerTargetSN[f.SN] = sn;
        }
        if (sn >= 0) {
            HumanAction(f.SN, sn);
            g_assigned.insert(f.SN);
        }
    }
}

bool UsrAI::isFlatArea(const tagInfo& info, int bdr, int bur, int size)
{
    if (info.theMap == nullptr) return false;
    if (bdr < 0 || bur < 0 || bdr + size > MAP_L || bur + size > MAP_U) return false;
    int h = -1;
    for (int i = bdr; i < bdr + size; i++) {
        for (int j = bur; j < bur + size; j++) {
            const tagTerrain& t = (*info.theMap)[i][j];
            if (t.type != MAPPATTERN_GRASS) return false;
            if (h < 0) h = t.height;
            else if (t.height != h) return false;
        }
    }
    return true;
}

bool UsrAI::findBuildPos(const tagInfo& info, int buildNum, int& bdr, int& bur, int maxRadius, int cx, int cy, bool outward)
{
    int size = (buildNum == BUILDING_HOME || buildNum == BUILDING_ARROWTOWER) ? 2 : 3;
    const double BLOCK = double(BLOCKSIDELENGTH);
    int cdr = cx, cur = cy;
    if (cx < 0 || cy < 0) {
        if (!centerBlockPos(info, cdr, cur)) return false;
    }

    auto occupied = [&](int i, int j) -> bool {
        const int M = 3;
        for (const auto& b : info.buildings) {
            int bs = (b.Type == BUILDING_HOME || b.Type == BUILDING_ARROWTOWER) ? 2 : 3;
            if (i - M < b.BlockDR + bs && b.BlockDR < i + size + M &&
                j - M < b.BlockUR + bs && b.BlockUR < j + size + M) return true;
        }

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
    }
    return false;
}

void UsrAI::controlBuilding(const tagInfo& info)
{

    bool bronzeCommitted = false;
    if (info.civilizationStage >= CIVILIZATION_BRONZEAGE) bronzeCommitted = true;
    for (const auto& b : info.buildings)
        if (b.Type == BUILDING_CENTER && b.Project == BUILDING_CENTER_UPGRADE)
            bronzeCommitted = true;

    auto tryBuild = [&](int buildNum) -> bool {
        int bdr = 0, bur = 0;

        if (buildNum == BUILDING_FARM) {
            int gdr = -1, gur = -1;
            for (const auto& b : info.buildings)
                if (b.Type == BUILDING_GRANARY) { gdr = b.BlockDR; gur = b.BlockUR; break; }
            if (!findBuildPos(info, buildNum, bdr, bur, 16, gdr, gur, true)
                && !findBuildPos(info, buildNum, bdr, bur, 16, gdr, gur, false)
                && !findBuildPos(info, buildNum, bdr, bur, 24)) return false;
        } else if (buildNum == BUILDING_ARROWTOWER) {

            {
                const double BLOCK = double(BLOCKSIDELENGTH);
                int pdr = -1, pur = -1;
                const int psn = findPriestSN(info);
                if (psn >= 0) {
                    for (const auto& a : info.armies)
                        if (a.SN == psn) { pdr = (int)(a.DR / BLOCK); pur = (int)(a.UR / BLOCK); break; }
                }
                int cdr0 = 0, cur0 = 0;
                bool hasCenter = centerBlockPos(info, cdr0, cur0);
                bool priestNearCenter = hasCenter && pdr >= 0
                    && std::abs(pdr - cdr0) + std::abs(pur - cur0) <= 12;
                bool ok = false;
                if (priestNearCenter) {
                    ok = findBuildPos(info, buildNum, bdr, bur, 12, pdr, pur, false)
                      || findBuildPos(info, buildNum, bdr, bur, 12, cdr0, cur0, false)
                      || findBuildPos(info, buildNum, bdr, bur, 24);
                } else {
                    ok = findBuildPos(info, buildNum, bdr, bur, 12, cdr0, cur0, false)
                      || findBuildPos(info, buildNum, bdr, bur, 24);
                }
                if (!ok) return false;
            }
        } else if (buildNum == BUILDING_STABLE || buildNum == BUILDING_MARKET
                   || buildNum == BUILDING_RANGE || buildNum == BUILDING_ARMYCAMP) {

            if (!findBuildPos(info, buildNum, bdr, bur, 24)
                && !findBuildPos(info, buildNum, bdr, bur, 36)) return false;
        } else if (!findBuildPos(info, buildNum, bdr, bur, 14, -1, -1, true)
                   && !findBuildPos(info, buildNum, bdr, bur, 24)) {
            return false;
        }
        for (const auto& f : info.farmers) {
            if (f.FarmerSort != FARMERTYPE_FARMER || f.NowState != HUMAN_STATE_IDLE) continue;
            if (g_buildAssigned.count(f.SN)) continue;
            if (g_assigned.count(f.SN)) continue;
            HumanBuild(f.SN, buildNum, bdr, bur);
            g_assigned.insert(f.SN);
            g_buildAssigned.insert(f.SN);
            g_buildDispatch[buildNum] = f.SN;
            g_lastBuildDR = bdr; g_lastBuildUR = bur;
            g_lastBuildSize = (buildNum == BUILDING_HOME || buildNum == BUILDING_ARROWTOWER) ? 2 : 3;
            g_buildSeq++;
            return true;
        }
        return false;
    };

    auto idleBuilding = [&](int type, int act, int meatNeed, int woodNeed, int stoneNeed, int goldNeed) {
        for (const auto& b : info.buildings) {
            if (b.Type == type && b.Percent >= 100 && b.Project == ACT_NULL
                && info.Meat >= meatNeed && info.Wood >= woodNeed
                && info.Stone >= stoneNeed && info.Gold >= goldNeed) {
                if (g_assigned.count(b.SN)) continue;
                BuildingAction(b.SN, act);
                g_assigned.insert(b.SN);
                return true;
            }
        }
        return false;
    };

    auto researchTech = [&](int buildType, int act, int meatNeed, int woodNeed, int stoneNeed, int goldNeed,
                            TechWatch& w, bool& done) {
        bool inResearch = false;
        for (const auto& b : info.buildings)
            if (b.Type == buildType && b.Project == act) { inResearch = true; break; }
        if (inResearch) { w.researching = true; w.frame = info.GameFrame; return; }
        if (w.researching) { done = true; w.researching = false; return; }
        if (info.GameFrame - w.frame > 600) {
            if (idleBuilding(buildType, act, meatNeed, woodNeed, stoneNeed, goldNeed))
                w.frame = info.GameFrame;
        }
    };

    auto ensureBuild = [&](int buildNum) -> bool {
        if (countBuildingBuilt(info, buildNum) >= 1) {
            g_buildDispatch.erase(buildNum);
            return true;
        }
        if (countBuilding(info, buildNum) >= 1) {
            g_buildDispatch.erase(buildNum);
            int unfinished = findUnfinishedBuilding(info, buildNum);
            if (unfinished >= 0) {
                for (const auto& f : info.farmers) {
                    if (f.FarmerSort != FARMERTYPE_FARMER || f.NowState != HUMAN_STATE_IDLE) continue;
                    if (g_assigned.count(f.SN)) continue;
                    HumanAction(f.SN, unfinished);
                    g_assigned.insert(f.SN);
                    return true;
                }
            }
            return true;
        }
        if (g_buildDispatch.count(buildNum)) {
            int sn = g_buildDispatch[buildNum];
            bool stillBuilding = false;
            for (const auto& f : info.farmers)
                if (f.SN == sn && f.NowState != HUMAN_STATE_IDLE) { stillBuilding = true; break; }
            if (stillBuilding) return false;
            g_buildDispatch.erase(buildNum);
        }
        return tryBuild(buildNum);
    };

    if (isWave3RushBronze(info)) {
        int req = (countBuildingBuilt(info, BUILDING_MARKET) > 0)
                + (countBuildingBuilt(info, BUILDING_RANGE) > 0)
                + (countBuildingBuilt(info, BUILDING_STABLE) > 0);

        if (req >= 2 && info.Meat >= 800) {
            for (const auto& b : info.buildings) {
                if (b.Type != BUILDING_CENTER || b.Percent < 100 || b.Project != ACT_NULL) continue;
                if (g_assigned.count(b.SN)) continue;
                BuildingAction(b.SN, BUILDING_CENTER_UPGRADE);
                g_assigned.insert(b.SN);
                return;
            }
        }

        if (req < 2) {
            if (countBuilding(info, BUILDING_STABLE) < 1 && info.Wood >= 150) { ensureBuild(BUILDING_STABLE); return; }
            if (countBuilding(info, BUILDING_MARKET) < 1 && info.Wood >= 150) { ensureBuild(BUILDING_MARKET); return; }
            if (countBuilding(info, BUILDING_RANGE) < 1 && info.Wood >= 150) { ensureBuild(BUILDING_RANGE); return; }
        }

        return;
    }

    if (bronzeCommitted && info.Human_MaxNum - info.Human_Num <= 4
        && countBuilding(info, BUILDING_HOME) < 10 && info.Wood >= 60) {
        tryBuild(BUILDING_HOME);
    }

    if (!bronzeCommitted && countBuilding(info, BUILDING_HOME) < 3
        && countBuilding(info, BUILDING_ARROWTOWER) >= 3
        && info.Wood >= 60) {
        tryBuild(BUILDING_HOME);
    }

    if (info.Wood >= 125)
        ensureBuild(BUILDING_ARMYCAMP);

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

    {
        bool researching = false;
        for (const auto& b : info.buildings)
            if (b.Type == BUILDING_GRANARY && b.Project == BUILDING_GRANARY_ARROWTOWER)
                researching = true;
        if (g_towerPhase == 0 && info.Meat >= 60) {

            for (const auto& b : info.buildings) {
                if (b.Type == BUILDING_GRANARY && b.Percent >= 100 && b.Project == ACT_NULL) {
                    if (g_assigned.count(b.SN)) continue;
                    BuildingAction(b.SN, BUILDING_GRANARY_ARROWTOWER);
                    g_assigned.insert(b.SN);
                    g_towerPhase = 1;
                    g_towerWaitFrame = info.GameFrame;
                    break;
                }
            }
        } else if (g_towerPhase == 1) {
            if (researching) { g_towerPhase = 2; g_towerStartFrame = info.GameFrame; }
            else if (info.GameFrame - g_towerWaitFrame > 300) g_towerPhase = 0;
        } else if (g_towerPhase == 2) {

            if (!researching && info.GameFrame - g_towerStartFrame > 300) { g_towerPhase = 3; towerResearched = true; }
            else if (!researching) g_towerPhase = 0;
        }

        bool towerUpgradeStarted = false;
        if (info.civilizationStage >= CIVILIZATION_BRONZEAGE && g_towerPhase == 3 && !g_towerUpgradeResearched) {
            towerUpgradeStarted = idleBuilding(BUILDING_GRANARY, BUILDING_GRANARY_ARROWTOWE_UPGRADE,
                                               BUILDING_GRANARY_UPGRADE_ARROWTOWER_FOOD, 0,
                                               BUILDING_GRANARY_UPGRADE_ARROWTOWER_STONE, 0);
            if (towerUpgradeStarted) g_towerUpgradeResearched = true;
        }

        const int towerLimit = (info.civilizationStage >= CIVILIZATION_BRONZEAGE)
            ? std::max(3, countBuildingBuilt(info, BUILDING_ARROWTOWER))
            : 3;

        if (info.GameFrame < WAVE3_FRAME && !towerUpgradeStarted && g_towerPhase == 3 && info.Stone >= 150) {
            int built = countBuildingBuilt(info, BUILDING_ARROWTOWER);
            int total = countBuilding(info, BUILDING_ARROWTOWER);

            if (g_buildDispatch.count(BUILDING_ARROWTOWER)) {
                int sn = g_buildDispatch[BUILDING_ARROWTOWER];
                bool busy = false;
                for (const auto& f : info.farmers)
                    if (f.SN == sn && f.NowState != HUMAN_STATE_IDLE) { busy = true; break; }
                if (total > built || !busy) g_buildDispatch.erase(BUILDING_ARROWTOWER);
            }

            if (built < towerLimit) {
                int unfinished = findUnfinishedBuilding(info, BUILDING_ARROWTOWER);
                if (unfinished >= 0) {
                    for (const auto& f : info.farmers) {
                        if (f.FarmerSort != FARMERTYPE_FARMER || f.NowState != HUMAN_STATE_IDLE) continue;
                        if (g_assigned.count(f.SN)) continue;
                        HumanAction(f.SN, unfinished);
                        g_assigned.insert(f.SN);
                        break;
                    }
                } else if (total == built && !g_buildDispatch.count(BUILDING_ARROWTOWER)) {
                    tryBuild(BUILDING_ARROWTOWER);
                }
            }
        }
    }

    if (info.Wood >= 150)
        ensureBuild(BUILDING_STABLE);

    if (info.Wood >= 150)
        ensureBuild(BUILDING_MARKET);

    if (info.Wood >= 150)
        ensureBuild(BUILDING_RANGE);

    {
        int farmLimit = (info.civilizationStage >= CIVILIZATION_BRONZEAGE) ? 6 : 3;

        bool farmTime = bronzeCommitted;
        if (info.Meat < FOOD_ALERT_THRESHOLD) { farmLimit += 2; farmTime = true; }
        int unfinished = findUnfinishedBuilding(info, BUILDING_FARM);
        if (unfinished >= 0 && farmTime) {
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
                   && countBuilding(info, BUILDING_FARM) < farmLimit * 2
                   && info.Wood >= 75) {
            tryBuild(BUILDING_FARM);
        }
    }

    if (!g_swordResearched && countBuildingBuilt(info, BUILDING_ARMYCAMP) >= 1) {
        if (idleBuilding(BUILDING_ARMYCAMP, BUILDING_ARMYCAMP_UPGRADE_CLUBMAN, 100, 0, 0, 0))
            g_swordResearched = true;
    }

    if (!g_meleeResearched && countBuildingBuilt(info, BUILDING_STOCK) >= 1 && info.Gold >= 200) {
        if (idleBuilding(BUILDING_STOCK, BUILDING_STOCK_UPGRADE_USETOOL, 100, 0, 0, 120))
            g_meleeResearched = true;
    }

    if (!g_woodUpgradeResearched && countBuildingBuilt(info, BUILDING_MARKET) >= 1) {
        if (idleBuilding(BUILDING_MARKET, BUILDING_MARKET_WOOD_UPGRADE, 120, 75, 0, 0))
            g_woodUpgradeResearched = true;
    }

    if (info.civilizationStage >= CIVILIZATION_BRONZEAGE) {

        if (info.Wood >= 120)
            ensureBuild(BUILDING_STOCK);

        if (countBuildingBuilt(info, BUILDING_STABLE) >= 1 && info.Wood >= 180)
            ensureBuild(BUILDING_COLLAGE);

        if (countBuildingBuilt(info, BUILDING_ARMYCAMP) >= 1) {
            researchTech(BUILDING_ARMYCAMP, BUILDING_ARMYCAMP_RESEARCH_LOGISTICS,
                         BUILDING_ARMYCAMP_RESEARCH_LOGISTICS_FOOD + scoutFoodReserve(info), 0, 0,
                         BUILDING_ARMYCAMP_RESEARCH_LOGISTICS_GOLD,
                         g_watchLogistics, g_logisticsResearched);
        }

        if (countBuildingBuilt(info, BUILDING_MARKET) >= 1) {
            researchTech(BUILDING_MARKET, BUILDING_MARKET_WHEEL_UPGRADE, 150 + scoutFoodReserve(info), 100, 0, 0,
                         g_watchWheel, g_wheelResearched);
        }

        if (countBuildingBuilt(info, BUILDING_RANGE) >= 1) {
            researchTech(BUILDING_RANGE, BUILDING_RANGE_UPGRADE_COMPOSITE_BOW, 180 + scoutFoodReserve(info), 100, 0, 0,
                         g_watchComposite, g_compositeResearched);
        }
    }
}

int UsrAI::countArmy(const tagInfo& info)
{
    int n = 0;
    for (const auto& a : info.armies) if (a.Sort != AT_PRIEST) n++;
    return n;
}

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

void UsrAI::controlScout(const tagInfo& info)
{
    const double BLOCK = double(BLOCKSIDELENGTH);

    if (!g_siegeKnown && info.GameFrame > 13500) {

        int visibleEnemies = 0;
        for (const auto& e : info.enemy_armies) if (e.Blood > 0) visibleEnemies++;
        const bool scoutReadyToPath = (info.GameFrame > 23000 && visibleEnemies < 4)
                                   || info.GameFrame > 26000;

        if (g_scoutSN >= 0) {
            bool alive = false;
            for (const auto& a : info.armies) if (a.SN == g_scoutSN) { alive = true; break; }
            if (!alive) {
                g_scoutSN = -1;
            }
        }

        int scoutSN = -1;
        for (const auto& a : info.armies) if (a.Sort == AT_SCOUT) { scoutSN = a.SN; break; }
        if (scoutSN < 0 && g_scoutSN < 0) {

            bool canAffordScout = info.civilizationStage >= CIVILIZATION_BRONZEAGE
                && info.Meat >= 100;
            for (const auto& b : info.buildings) {
                if (b.Type != BUILDING_STABLE || b.Percent < 100 || b.Project != ACT_NULL) continue;
                if (g_assigned.count(b.SN)) continue;
                if (canAffordScout) {
                    BuildingAction(b.SN, BUILDING_STABLE_CREATE_SCOUT);
                    g_assigned.insert(b.SN);
                    break;
                }
            }
        } else {
            if (scoutSN >= 0 && scoutSN != g_scoutSN) {

                g_scoutSN = scoutSN;
                g_scoutTrainFrame = info.GameFrame;
                g_scoutPhase = 0;
                g_scoutNoProgressFrame = 0;
                g_scoutNoProgressBX = -1;
                g_scoutNoProgressBY = -1;
                g_scoutPath.clear();
                g_scoutLastOrderFrame = info.GameFrame;
            } else if (scoutSN >= 0) {
                g_scoutSN = scoutSN;
            }

            if (enemySiegePos(info, g_siegeKnownDR, g_siegeKnownUR)) {
                g_siegeKnown = true;
            } else if (scoutReadyToPath) {

                const tagArmy* scout = nullptr;
                for (const auto& a : info.armies) if (a.SN == g_scoutSN) { scout = &a; break; }
                if (scout && scout->NowState == HUMAN_STATE_IDLE
                    && info.GameFrame - g_scoutLastOrderFrame > 45) {

                    int cb = (int)(scout->DR / BLOCK), cu = (int)(scout->UR / BLOCK);

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

                    double gx, gy;
                    {
                        int cdr = MAP_L / 2, cur = MAP_U / 2;
                        centerBlockPos(info, cdr, cur);

                        int mdx = (MAP_L - 1 - cdr) - cdr;
                        int mdy = (MAP_U - 1 - cur) - cur;
                        int dx = mdx, dy = mdy;

                        int dir = g_scoutPhase / 3;
                        int lane = g_scoutPhase % 3;
                        switch (dir & 3) {
                        case 0:  dx = mdx;  dy = mdy;  break;
                        case 1:  dx = mdx;  dy = -mdy; break;
                        case 2:  dx = mdx;  dy = 0;    break;
                        default: dx = 0;    dy = mdy;  break;
                        }
                        int off = (lane == 0) ? 0 : ((lane == 1) ? -7 : 7);

                        const int LO = 2, HI_DR = MAP_L - 1 - 2, HI_UR = MAP_U - 1 - 2;
                        double tDR = (dx > 0) ? double(HI_DR - cdr) / dx
                                   : (dx < 0 ? double(LO - cdr) / dx : 1e18);
                        double tUR = (dy > 0) ? double(HI_UR - cur) / dy
                                   : (dy < 0 ? double(LO - cur) / dy : 1e18);
                        double t = std::min(tDR, tUR);
                        if (t > 1e17) t = 0;
                        int eDR = cdr + int(dx * t), eUR = cur + int(dy * t);

                        if (off != 0) {
                            double pl = std::sqrt(double(dx * dx) + double(dy * dy));
                            if (pl > 0.01) {
                                double px = -dy / pl, py = dx / pl;
                                eDR += (int)std::lround(px * off);
                                eUR += (int)std::lround(py * off);
                                eDR = std::max(LO, std::min(eDR, HI_DR));
                                eUR = std::max(LO, std::min(eUR, HI_UR));
                            }
                        }
                        gx = (eDR + 0.5) * BLOCK;
                        gy = (eUR + 0.5) * BLOCK;
                    }
                    double dx = gx - scout->DR, dy = gy - scout->UR;
                    double dl = std::sqrt(dx * dx + dy * dy);

                    if (dl <= 2 * BLOCK) {
                        g_scoutPhase++;
                        g_scoutNoProgressBX = -1;
                        g_scoutNoProgressBY = -1;
                        g_scoutLastOrderFrame = info.GameFrame;
                        return;
                    }
                    double step = std::min(dl, 7.0 * BLOCK);
                    int tb = (int)((scout->DR + dx / dl * step) / BLOCK);
                    int tu = (int)((scout->UR + dy / dl * step) / BLOCK);
                    if (tb == cb && tu == cu) { g_scoutLastOrderFrame = info.GameFrame; return; }

                    int bi = tb, bj = tu;
                    bool idealOk = isWalkable(info, tb, tu) && obstacleClear(info, tb, tu, 2);
                    if (!idealOk) {
                        bool found = false;
                        for (int r = 1; r <= 8 && !found; r++) {
                            int bestI = -1, bestJ = -1; double bestD = 1e18;
                            for (int i = tb - r; i <= tb + r; i++) {
                                for (int j = tu - r; j <= tu + r; j++) {
                                    if (abs(i - tb) != r && abs(j - tu) != r) continue;

                                    if (i == cb && j == cu) continue;
                                    if (!isWalkable(info, i, j) || !obstacleClear(info, i, j, 2)) continue;
                                    double dd = (i - tb) * (i - tb) + (j - tu) * (j - tu);
                                    if (dd < bestD) { bestD = dd; bestI = i; bestJ = j; }
                                }
                            }
                            if (bestI >= 0) { bi = bestI; bj = bestJ; found = true; }
                        }
                        if (!found) {
                            for (int r = 1; r <= 8 && !found; r++) {
                                int bestI = -1, bestJ = -1; double bestD = 1e18;
                                for (int i = tb - r; i <= tb + r; i++) {
                                    for (int j = tu - r; j <= tu + r; j++) {
                                        if (abs(i - tb) != r && abs(j - tu) != r) continue;
                                        if (i == cb && j == cu) continue;
                                        if (!isWalkable(info, i, j)) continue;
                                        double dd = (i - tb) * (i - tb) + (j - tu) * (j - tu);
                                        if (dd < bestD) { bestD = dd; bestI = i; bestJ = j; }
                                    }
                                }
                                if (bestI >= 0) { bi = bestI; bj = bestJ; found = true; }
                            }
                            if (!found) {

                                double ux = dx / dl, uy = dy / dl;
                                int bestI = -1, bestJ = -1; double bestProj = -1e18;
                                for (int r = 1; r <= 5 && bestI < 0; r++) {
                                    for (int i = cb - r; i <= cb + r; i++) {
                                        for (int j = cu - r; j <= cu + r; j++) {
                                            if (i == cb && j == cu) continue;
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

                    {
                        auto best = bfsBestToward(cb, cu, gx, gy, 7);
                        if (best.first == cb && best.second == cu) {
                            double ux = dx / dl, uy = dy / dl;
                            double curD = calDistance((cb + 0.5) * BLOCK, (cu + 0.5) * BLOCK, gx, gy);
                            int slideI = -1, slideJ = -1; double bestScore = -1e18;
                            for (int r = 1; r <= 5; r++) {
                                for (int i = cb - r; i <= cb + r; i++) {
                                    for (int j = cu - r; j <= cu + r; j++) {
                                        if (i == cb && j == cu) continue;
                                        if (!isWalkable(info, i, j)) continue;
                                        double proj = (i - cb) * ux + (j - cu) * uy;
                                        double candD = calDistance((i + 0.5) * BLOCK, (j + 0.5) * BLOCK, gx, gy);
                                        double extra = candD - curD; if (extra < 0) extra = 0;
                                        double score = proj - 0.5 * extra;
                                        if (score > bestScore) { bestScore = score; slideI = i; slideJ = j; }
                                    }
                                }
                            }
                            if (slideI >= 0) {
                                bi = slideI; bj = slideJ;
                            } else {

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

                }
            } else {

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

    bool prepareUpgrade = false;
    if (info.civilizationStage == CIVILIZATION_TOOLAGE && info.Meat >= 700) {
        int tb = (countBuildingBuilt(info, BUILDING_MARKET) > 0)
               + (countBuildingBuilt(info, BUILDING_RANGE) > 0)
               + (countBuildingBuilt(info, BUILDING_STABLE) > 0);
        prepareUpgrade = (tb >= 2);
    }

    const int armyCap = (info.civilizationStage >= CIVILIZATION_BRONZEAGE)
        ? (g_underAttack ? 30 : 26)
        : (g_underAttack ? 8 : 5);
    int queuedUnits = 0;
    auto canTrain = [&]() {
        return countArmy(info) + queuedUnits < armyCap
            && info.Human_Num + queuedUnits < info.Human_MaxNum - 3;
    };

    const int scoutReserve = scoutFoodReserve(info);
    auto meatFor = [&](int cost) { return info.Meat >= cost + scoutReserve; };

    const bool forbidTrain = isWave3RushBronze(info);

    if (!prepareUpgrade && !forbidTrain) {

    for (const auto& b : info.buildings) {
        if (b.Type != BUILDING_ARMYCAMP || b.Percent < 100 || b.Project != ACT_NULL) continue;
        if (g_assigned.count(b.SN)) continue;
        if (!canTrain()) continue;
        if (info.civilizationStage == CIVILIZATION_TOOLAGE && info.GameFrame > 2500) {

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

            if (meatFor(50)) {
                BuildingAction(b.SN, BUILDING_ARMYCAMP_CREATE_CLUBMAN);
                g_assigned.insert(b.SN);
                queuedUnits++;
                continue;
            }
        }
    }

    for (const auto& b : info.buildings) {
        if (b.Type != BUILDING_RANGE || b.Percent < 100 || b.Project != ACT_NULL) continue;
        if (g_assigned.count(b.SN)) continue;
        if (!canTrain()) continue;
        if (info.civilizationStage >= CIVILIZATION_BRONZEAGE) {

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

    if (info.civilizationStage >= CIVILIZATION_BRONZEAGE) {

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

        for (const auto& b : info.buildings) {
            if (b.Type != BUILDING_STABLE || b.Percent < 100 || b.Project != ACT_NULL) continue;
            if (g_assigned.count(b.SN)) continue;
            if (!canTrain()) continue;

            if (meatFor(70) && info.Gold >= 120) {
                BuildingAction(b.SN, BUILDING_STABLE_CREATE_CAVALRY);
                g_assigned.insert(b.SN);
                queuedUnits++;
            }
        }
    }
    }

    bool offense = (info.GameFrame > 21000 && countArmy(info) >= 12)
                || info.GameFrame > 26000;
    double targetDR = 0, targetUR = 0;
    bool hasTarget = false;
    if (offense) {

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

    int enemiesNearSiege = -1;
    if (hasTarget) {
        enemiesNearSiege = 0;
        for (const auto& e : info.enemy_armies)
            if (e.Blood > 0 && calDistance(e.DR, e.UR, targetDR, targetUR) <= 25 * BLOCK) enemiesNearSiege++;
        for (const auto& f : info.enemy_farmers)
            if (f.Blood > 0 && calDistance(f.DR, f.UR, targetDR, targetUR) <= 25 * BLOCK) enemiesNearSiege++;
    }

    double armyDR = 0, armyUR = 0;
    bool hasArmy = armyCenterPos(info, armyDR, armyUR);
    bool armyAtSiege = hasTarget && hasArmy
        && calDistance(armyDR, armyUR, targetDR, targetUR) <= 20 * BLOCK;

    bool cleared = armyAtSiege && enemiesNearSiege == 0;

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
            if (!found) return;
        }
        HumanMove(sn, (bi + 0.5) * BLOCK, (bj + 0.5) * BLOCK);
        g_armyLastOrderFrame[sn] = info.GameFrame;
    };

    auto scatterPoint = [&](int sn, double gx, double gy) -> std::pair<double, double> {

        int slot = sn % 10;
        double ang = slot * (2 * 3.14159265358979 / 10.0);
        double r = (2.0 + (sn % 3) * 0.8) * BLOCK;
        return std::make_pair(gx + std::cos(ang) * r, gy + std::sin(ang) * r);
    };

    int priestSN = findPriestSN(info);
    int priestAttacker = -1;
    double attackerDR = 0, attackerUR = 0;
    bool priestUnderAttack = false;
    if (priestSN >= 0) {
        priestAttacker = findAttackerSN(info, priestSN);
        if (priestAttacker >= 0 && enemyDetailPos(info, priestAttacker, attackerDR, attackerUR))
            priestUnderAttack = true;
    }

    static std::map<int, int> g_throwerRetreatFrame;

    for (const auto& a : info.armies) {
        if (a.Sort == AT_PRIEST) continue;
        if (a.Sort == AT_SCOUT) continue;
        const bool ranged = isRangedUnit(a.Sort);

        if (a.NowState != HUMAN_STATE_IDLE && !(ranged && a.NowState == HUMAN_STATE_ATTACKING))
            continue;

        if (a.NowState == HUMAN_STATE_IDLE && priestUnderAttack
            && calDistance(a.DR, a.UR, attackerDR, attackerUR) <= 15 * BLOCK) {
            HumanAction(a.SN, priestAttacker);
            continue;
        }

        if (offense) {
            double nd = 1e18;
            int enemy = nearestEnemySN(info, a.DR, a.UR, nd);

            if (enemy >= 0 && isSiegeBuildingSN(info, enemy)) enemy = -1;

            if (enemy >= 0 && enemy == g_priestConvertTargetSN) enemy = -1;

            if (ranged) {
                double kx = 0, ky = 0; double ndK = 1e18;
                int nk = nearestEnemySN(info, a.DR, a.UR, ndK);
                if (nk >= 0 && enemyDetailPos(info, nk, kx, ky)) {
                    if (a.Sort == AT_STONE_THROWER) {

                        if (ndK < 4 * BLOCK) {

                            auto itRet = g_throwerRetreatFrame.find(a.SN);
                            const bool inRetreatCd = (itRet != g_throwerRetreatFrame.end())
                                                  && (info.GameFrame - itRet->second < 60);
                            if (a.NowState == HUMAN_STATE_WALKING && inRetreatCd) {
                                continue;
                            }
                            double rx = a.DR - kx, ry = a.UR - ky;
                            double rl = std::sqrt(rx * rx + ry * ry);
                            double sx = a.DR, sy = a.UR;
                            if (rl > 1) { sx = a.DR + rx / rl * 10 * BLOCK; sy = a.UR + ry / rl * 10 * BLOCK; }
                            sx = fmax(BLOCK, fmin(sx, (MAP_L - 1) * BLOCK));
                            sy = fmax(BLOCK, fmin(sy, (MAP_U - 1) * BLOCK));
                            auto sp = scatterPoint(a.SN, sx, sy);
                            moveArmyTo(a.SN, sp.first, sp.second);
                            g_throwerRetreatFrame[a.SN] = info.GameFrame;
                            continue;
                        }

                    } else if (ndK < 8 * BLOCK) {
                        double rx = a.DR - kx, ry = a.UR - ky;
                        double rl = std::sqrt(rx * rx + ry * ry);
                        double sx = a.DR, sy = a.UR;
                        if (rl > 1) { sx = a.DR + rx / rl * 12 * BLOCK; sy = a.UR + ry / rl * 12 * BLOCK; }
                        sx = fmax(BLOCK, fmin(sx, (MAP_L - 1) * BLOCK));
                        sy = fmax(BLOCK, fmin(sy, (MAP_U - 1) * BLOCK));
                        auto sp = scatterPoint(a.SN, sx, sy);
                        moveArmyTo(a.SN, sp.first, sp.second);
                        continue;
                    }
                }
            }

            if (enemy >= 0) {

                bool canAttack = ranged ? (a.NowState == HUMAN_STATE_IDLE)
                                        : (a.NowState == HUMAN_STATE_IDLE || nd <= 8 * BLOCK);
                if (canAttack && (ranged || cleared || nd <= 8 * BLOCK)) {
                    HumanAction(a.SN, enemy);
                }

            }
            if (enemy < 0 || (!ranged && !cleared && nd > 8 * BLOCK)) {

                if (hasTarget) {
                    if (ranged) {

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

                        double dx = a.DR - targetDR, dy = a.UR - targetUR;
                        double dist = std::sqrt(dx * dx + dy * dy);
                        if (dist > 20 * BLOCK) {
                            auto sp = scatterPoint(a.SN, targetDR, targetUR);
                            moveArmyTo(a.SN, sp.first, sp.second);
                        } else if (dist < 15 * BLOCK) {
                            auto sp = scatterPoint(a.SN,
                                targetDR + dx / dist * 18 * BLOCK,
                                targetUR + dy / dist * 18 * BLOCK);
                            moveArmyTo(a.SN, sp.first, sp.second);
                        }

                    }
                }
            }
        } else {

            int towerTarget = -1; double towerDist = 1e18;
            int nearTarget  = -1; double nearDist  = 1e18;
            auto considerTarget = [&](int sn, double dr, double ur) {
                if (isSiegeBuildingSN(info, sn)) return;
                if (sn == g_priestConvertTargetSN) return;
                double d = calDistance(a.DR, a.UR, dr, ur);
                if (isInTowerRange(info, dr, ur) && d < towerDist) { towerDist = d; towerTarget = sn; }
                if (d < nearDist) { nearDist = d; nearTarget = sn; }
            };
            for (const auto& e : info.enemy_armies)
                if (e.Blood > 0) considerTarget(e.SN, e.DR, e.UR);
            for (const auto& f : info.enemy_farmers)
                if (f.Blood > 0) considerTarget(f.SN, f.DR, f.UR);

            int enemy = nearTarget;
            if (towerTarget >= 0
                && (towerDist <= nearDist * 2.0 || towerDist <= 20 * BLOCK))
                enemy = towerTarget;
            if (enemy >= 0 && a.NowState == HUMAN_STATE_IDLE) {
                HumanAction(a.SN, enemy);
            } else {

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

void UsrAI::controlFarmerDefense(const tagInfo& info)
{
    const double BLOCK = double(BLOCKSIDELENGTH);
    const double ALERT_RANGE = 15 * BLOCK;
    const double CLEAR_RANGE = 20 * BLOCK;

    {
        bool bronzeCommitted = false;
        if (info.civilizationStage >= CIVILIZATION_BRONZEAGE) bronzeCommitted = true;
        for (const auto& b : info.buildings)
            if (b.Type == BUILDING_CENTER && b.Project == BUILDING_CENTER_UPGRADE)
                bronzeCommitted = true;
        if (!bronzeCommitted) return;
    }

    double cdx = 0, cdy = 0;
    bool hasCenter = false;
    for (const auto& b : info.buildings)
        if (b.Type == BUILDING_CENTER) {
            cdx = (b.BlockDR + 0.5) * BLOCK; cdy = (b.BlockUR + 0.5) * BLOCK; hasCenter = true; break;
        }

    double minDist = 1e18;
    for (const auto& a : info.enemy_armies) {
        if (a.Blood <= 0) continue;
        double d = hasCenter ? calDistance(cdx, cdy, a.DR, a.UR) : 0.0;
        if (hasCenter && d < minDist) minDist = d;
    }

    if (g_underAttack) {
        if (minDist >= CLEAR_RANGE) {
            g_underAttack = false;

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

    if (!g_underAttack) return;

    std::set<int> targeted;
    for (const auto& a : info.enemy_armies)
        if (a.WorkObjectSN >= 0) targeted.insert(a.WorkObjectSN);
    for (const auto& e : info.enemy_farmers)
        if (e.WorkObjectSN >= 0) targeted.insert(e.WorkObjectSN);

    std::vector<std::pair<double,int>> idleList;
    for (const auto& f : info.farmers) {
        if (f.FarmerSort != FARMERTYPE_FARMER || f.NowState != HUMAN_STATE_IDLE) continue;
        if (g_assigned.count(f.SN)) continue;
        double nd = 1e18;
        int enemySN = nearestEnemyUnitSN(info, f.DR, f.UR, nd);
        if (enemySN >= 0) idleList.push_back(std::make_pair(nd, f.SN));
    }
    std::sort(idleList.begin(), idleList.end());

    std::set<int> defenders;
    for (size_t i = 0; i < idleList.size() && i < 5; i++)
        defenders.insert(idleList[i].second);
    for (const auto& f : info.farmers) {
        if (f.FarmerSort != FARMERTYPE_FARMER || f.NowState != HUMAN_STATE_IDLE) continue;
        if (g_assigned.count(f.SN)) continue;
        if (targeted.count(f.SN)) defenders.insert(f.SN);
    }

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

void UsrAI::controlTowers(const tagInfo& info)
{
    const double BLOCK = double(BLOCKSIDELENGTH);
    const double TOWER_RANGE = 7 * BLOCK;
    const int    COOLDOWN = 45;

    for (const auto& b : info.buildings) {
        if (b.Type != BUILDING_ARROWTOWER || b.Percent < 100) continue;

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
            if (it != g_towerCmd.end()) g_towerCmd.erase(it);
            continue;
        }

        if (it != g_towerCmd.end() && it->second.first == bestSN
            && info.GameFrame - it->second.second < COOLDOWN) continue;

        HumanAction(b.SN, bestSN);
        g_towerCmd[b.SN] = std::make_pair(bestSN, info.GameFrame);
    }
}

void UsrAI::detectStuck(const tagInfo& info)
{
    const double BLOCK = double(BLOCKSIDELENGTH);
    for (const auto& f : info.farmers) {
        if (f.FarmerSort != FARMERTYPE_FARMER) continue;
        if (g_assigned.count(f.SN)) continue;
        if (f.NowState == HUMAN_STATE_WORKING) continue;
        if (f.NowState == HUMAN_STATE_ATTACKING) continue;
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

            int stuckThreshold = (f.NowState == HUMAN_STATE_IDLE) ? 120 : 240;
            if (g_stuckFrame[f.SN] >= stuckThreshold) {
                int bdr = 0, bur = 0;
                if (centerBlockPos(info, bdr, bur)) {
                    HumanMove(f.SN, (bdr + 1.5) * BLOCK, (bur + 1.5) * BLOCK);
                    g_stuckCooldown[f.SN] = info.GameFrame + 600;
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

