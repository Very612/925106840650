#ifndef USRAI_H
#define USRAI_H

#include "ai.h"
#include <unordered_map>

extern tagGame tagUsrGame;
extern ins UsrIns;
/*##########DO NOT MODIFY THE CODE ABOVE##########*/

class UsrAI:public AI
{
public:
    UsrAI(){this->id=0;}
    ~UsrAI(){}

private:
    void processData() override;
    tagInfo getInfo(){return tagUsrGame.getInfo();}
    int AddToIns(instruction ins) override
    {
        UsrIns.lock.lock();
        ins.id=UsrIns.g_id;
        UsrIns.g_id++;
        UsrIns.instructions.push(ins);
        UsrIns.lock.unlock();
        return ins.id;
    }
    void clearInsRet() override
    {
        tagUsrGame.clearInsRet();
    }
    /*##########DO NOT MODIFY THE CODE IN THE CLASS##########*/

    void controlPriest(const tagInfo& info);
    int  findPriestSN(const tagInfo& info);
    bool enemyDetailPos(const tagInfo& info, int SN, double& dr, double& ur);
    int  nearestEnemySN(const tagInfo& info, double pr, double pu, double& outDist);
    int  nearestEnemyUnitSN(const tagInfo& info, double pr, double pu, double& outDist);
    int  findAttackerSN(const tagInfo& info, int priestSN);
    int  findWoundedAllySN(const tagInfo& info, int priestSN);
    bool centerBlockPos(const tagInfo& info, int& bdr, int& bur);

    void controlEconomy(const tagInfo& info);
    void controlBuilding(const tagInfo& info);
    int  countFarmers(const tagInfo& info);
    int  countBuilding(const tagInfo& info, int type);
    int  countBuildingBuilt(const tagInfo& info, int type);
    int  nearestResourceSN(const tagInfo& info, double pr, double pu, int resClass);
    int  nearestFarmSN(const tagInfo& info, double pr, double pu);
    int  pickResourceClass(const tagInfo& info, int idx);
    bool findBuildPos(const tagInfo& info, int buildNum, int& bdr, int& bur, int maxRadius = 24,
                      int cx = -1, int cy = -1, bool outward = false);
    bool isFlatArea(const tagInfo& info, int bdr, int bur, int size);

    void controlMilitary(const tagInfo& info);
    void controlScout(const tagInfo& info);
    void controlTowers(const tagInfo& info);
    int  countArmy(const tagInfo& info);
    bool enemySiegePos(const tagInfo& info, double& dr, double& ur);

    void detectStuck(const tagInfo& info);
    void controlFarmerDefense(const tagInfo& info);

    bool towerResearched = false;

};

/*##########YOUR CODE BEGINS HERE##########*/

/*##########YOUR CODE ENDS HERE##########*/
#endif

