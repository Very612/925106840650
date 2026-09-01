#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
newAOE AI 日志诊断工具
=====================
用法:
    python analyze_ai_log.py <日志文件> [选项]

示例:
    python analyze_ai_log.py smoke.log
    python analyze_ai_log.py smoke.log --wave3 21000 --ranged-min 8 --osc 8

先让游戏把 [STAT] 日志重定向到文件:
    newAOE.exe -freq MAX -exam -offscreen -map map.njust > smoke.log 2>&1

支持多局一起看:
    把多局输出用 >> 追加到同一个文件即可，脚本会自动按 session_start 切分，
    先打印「逐局汇总对比表」，再逐局打印详细报告。
    例: newAOE.exe ... >> all.log 2>&1   (每局都追加到 all.log)

检查项:
    1. 祭司是否阵亡（含"反攻期/总攻后"是否死亡）
    2. 转化是否发生（总数 / 第三波之后各多少次）
    3. 转化目标是不是高价值单位（投石车 sort=8）
    3b. 擦边转化（转化时距目标距离，上限 12 格，判断是否保持自身攻击距离）
    4. 祭司是否"来回走"（振荡/折返检测）
    5. 第三波之后是否还在建箭塔（应为 0）
    6. 总攻期远程兵是否贴脸（进敌堆）
    7. 总攻开始时视野内有没有敌人（解释"无转化"是不是因为看不见）
    8. 侦察兵是否成功探路（探到敌方攻城厂 / 阵亡 / 原地不动 / 打转绕圈）
    9. 马厩 / 侦察兵是否成功产出
"""

import sys
import re
import math
from collections import Counter, defaultdict

# 兵种枚举（与 config.h 的 enum AT_ARMY 一致）
ARMY_NAMES = {
    0:  "棍棒兵",
    1:  "投石兵",
    2:  "弓箭手",
    3:  "侦察兵",
    4:  "短剑兵",
    5:  "强化兵",
    6:  "骑兵",
    7:  "船",
    8:  "投石车",
    9:  "祭司",
    10: "方阵兵",
    11: "战车",
    12: "战车弓箭手",
    13: "阔剑兵",
    14: "复合弓兵",
}
STONE_THROWER = 8

OK, WARN, BAD = "PASS", "WARN", "FAIL"


def parse_log(path):
    """解析 [STAT] 行 -> 事件列表 [(name, {k: v}), ...]"""
    events = []
    pat = re.compile(r"^\[STAT\]\s+(\S+)\s*(.*)$")
    with open(path, "r", encoding="utf-8", errors="replace") as f:
        for line in f:
            m = pat.match(line.strip())
            if not m:
                continue
            name, rest = m.group(1), m.group(2)
            kv = {}
            toks = rest.split()
            for i in range(0, len(toks) - 1, 2):
                key, val = toks[i], toks[i + 1]
                try:
                    kv[key] = int(val)
                except ValueError:
                    try:
                        kv[key] = float(val)
                    except ValueError:
                        kv[key] = val
            events.append((name, kv))
    return events


def get_int(kv, *keys, default=None):
    for k in keys:
        if k in kv and isinstance(kv[k], (int, float)):
            return int(kv[k])
    return default


def section(title):
    print("\n" + "=" * 58)
    print(title)
    print("=" * 58)


def check(status, msg, detail=""):
    print(f"[{status}] {msg}")
    if detail:
        for d in str(detail).splitlines():
            print(f"        {d}")


def analyze_run(title, events, WAVE3, RANGED_SAFE, OSC_LIMIT):
    """对一次运行的日志做完整诊断"""
    by = defaultdict(list)
    for name, kv in events:
        by[name].append(kv)

    section(f"AI 日志诊断报告  |  {title}")
    print(f"STAT 事件总数: {len(events)}   事件种类: {len(by)}")

    # ---------- 里程碑 ----------
    section("里程碑时间线")
    order = ["session_start", "stable_built", "bronze_done", "scout_trained",
             "scout_path_start", "siege_found", "wave3_arrive", "offense_start"]
    for key in order:
        if key not in by:
            continue
        kv = by[key][0]
        fr = get_int(kv, "frame", default="?")
        extra = " ".join(f"{k}={v}" for k, v in kv.items() if k != "frame")
        print(f"  {key:<15} frame {fr}   {extra}")
    if "priest_died" in by:
        for kv in by["priest_died"]:
            print(f"  {'priest_died':<15} frame {get_int(kv, 'frame', default='?')}   <<< 祭司阵亡")
    if "scout_died" in by:
        for kv in by["scout_died"]:
            print(f"  {'scout_died':<15} frame {get_int(kv, 'frame', default='?')}   <<< 侦察兵阵亡")

    frames = [get_int(kv, "frame") for _, kv in events if get_int(kv, "frame") is not None]
    if frames:
        print(f"\n  日志帧范围: {min(frames)} ~ {max(frames)}")

    # ---------- 检查 1: 祭司阵亡 ----------
    section("检查项")
    deaths = by.get("priest_died", [])
    if deaths:
        check(BAD, f"祭司阵亡 {len(deaths)} 次",
              "\n".join(f"frame {get_int(kv, 'frame')}" for kv in deaths))
    else:
        check(OK, "祭司全程存活（无 priest_died 事件）")

    # ---------- 检查 1b: 反攻期(总攻后)祭司死亡 ----------
    if deaths and "offense_start" in by:
        off_fr = get_int(by["offense_start"][0], "frame")
        off_deaths = [kv for kv in deaths if (get_int(kv, "frame") or 0) > (off_fr or 0)]
        if off_deaths:
            check(BAD, f"反攻期（总攻后）祭司阵亡 {len(off_deaths)} 次",
                  "\n".join(f"frame {get_int(kv, 'frame')}" for kv in off_deaths))
        else:
            check(OK, "反攻期祭司未阵亡（死亡都发生在总攻前）")

    # ---------- 检查 2: 转化 ----------
    picks = by.get("convert_pick", [])
    starts = by.get("priest_convert_start", [])
    picks_total = len(picks)
    picks_after = [kv for kv in picks if (get_int(kv, "frame") or 0) > WAVE3]
    starts_after = [kv for kv in starts if (get_int(kv, "frame") or 0) > WAVE3]

    if picks_total == 0:
        check(BAD, "全程没有任何转化目标被选中（祭司从不转化）")
    else:
        check(OK, f"祭司共选中转化目标 {picks_total} 次"
                  f"（其中第三波 {WAVE3} 帧之后 {len(picks_after)} 次）")
        if starts:
            check(OK, f"实际进入射程并开始转化 {len(starts)} 次"
                      f"（第三波后 {len(starts_after)} 次）")
        else:
            check(WARN, "有选中目标，但从未进入转化射程（可能一直在追 / 被绕行卡住）")

    # ---------- 检查 3: 转化目标价值 ----------
    if picks:
        cnt = Counter(get_int(kv, "sort", default=-1) for kv in picks)
        lines = []
        for s, c in cnt.most_common():
            nm = ARMY_NAMES.get(s, f"未知({s})")
            mark = "  <== 高价值(投石车)" if s == STONE_THROWER else ""
            lines.append(f"{nm:<12} {c} 次{mark}")
        thrower_cnt = cnt.get(STONE_THROWER, 0)
        if thrower_cnt:
            check(OK, f"转化目标含高价值单位：投石车 {thrower_cnt} 次", "\n".join(lines))
        else:
            check(WARN, "转化目标中没有任何投石车（都是普通兵种）", "\n".join(lines))

    # ---------- 检查 3b: 擦边转化（转化时距目标距离，上限 12 格）----------
    if starts:
        ds = [get_int(kv, "d") for kv in starts if get_int(kv, "d") is not None]
        if ds:
            edge = sum(1 for d in ds if d >= 10)     # 距上限 2 格内 = 擦边
            close = sum(1 for d in ds if d <= 8)     # 8 格内 = 贴脸
            if close:
                check(WARN, f"转化距离偏近：{len(ds)} 次转化，最近 {min(ds)} 格，"
                            f"擦边(>=10格) {edge} 次 / 贴脸(<=8格) {close} 次",
                      f"各次转化距离: {sorted(ds)}")
            else:
                check(OK, f"擦边转化：{len(ds)} 次转化全部 >= 9 格（保持自身攻击距离）",
                      f"各次转化距离: {sorted(ds)}")
        else:
            print("[--] 转化日志无距离字段（旧日志）")

    # ---------- 检查 4: 祭司振荡（来回走）----------
    moves = [kv for kv in by.get("priest_move", [])]
    moves.sort(key=lambda kv: get_int(kv, "frame") or 0)
    if len(moves) >= 3:
        reversals = 0
        pingpong = 0
        prev_v = None
        for i in range(1, len(moves)):
            f0, f1 = get_int(moves[i - 1], "frame"), get_int(moves[i], "frame")
            x0, y0 = get_int(moves[i - 1], "dr", default=0), get_int(moves[i - 1], "ur", default=0)
            x1, y1 = get_int(moves[i], "dr", default=0), get_int(moves[i], "ur", default=0)
            vx, vy = x1 - x0, y1 - y0
            ln = math.hypot(vx, vy)
            if ln < 1:
                continue
            if prev_v is not None:
                pv = prev_v
                pl = math.hypot(*pv)
                if pl > 0:
                    cosang = (vx * pv[0] + vy * pv[1]) / (ln * pl)
                    gap = (f1 or 0) - (f0 or 0)
                    if cosang < -0.5 and gap <= 600:   # 掉头 >120°
                        reversals += 1
            prev_v = (vx, vy)
            if i >= 2:
                xb, yb = get_int(moves[i - 2], "dr", default=0), get_int(moves[i - 2], "ur", default=0)
                if math.hypot(x1 - xb, y1 - yb) <= 4:
                    pingpong += 1
        if reversals >= OSC_LIMIT or pingpong >= OSC_LIMIT:
            check(BAD, f"祭司疑似来回走：掉头 {reversals} 次 / 折返回原点 {pingpong} 次"
                       f"（阈值 {OSC_LIMIT}）",
                  f"共 {len(moves)} 条移动指令")
        else:
            check(OK, f"祭司移动正常：掉头 {reversals} 次 / 折返 {pingpong} 次"
                      f"（阈值 {OSC_LIMIT}）",
                  f"共 {len(moves)} 条移动指令")
    else:
        print(f"[--] 祭司移动指令不足（{len(moves)} 条），跳过振荡检测")

    # ---------- 检查 5: 第三波后是否还在建箭塔 ----------
    towers = by.get("tower_build", [])
    if towers:
        last = max(get_int(kv, "frame") or 0 for kv in towers)
        after = [kv for kv in towers if (get_int(kv, "frame") or 0) > WAVE3]
        if after:
            check(BAD, f"第三波({WAVE3}帧)之后仍在建箭塔 {len(after)} 次",
                  "\n".join(f"frame {get_int(kv, 'frame')} action={kv.get('action')}"
                            for kv in after[:10]))
        else:
            check(OK, f"第三波后已停建箭塔（共 {len(towers)} 次，最后一次 frame {last}）")
    else:
        print("[--] 无 tower_build 事件（本局没有建造箭塔）")

    # ---------- 检查 6: 总攻期阵型（远程是否贴脸）----------
    forms = by.get("formation", [])
    if forms:
        rmin = [get_int(kv, "ranged_min") for kv in forms if get_int(kv, "ranged_min") is not None]
        rmin = [v for v in rmin if v >= 0]
        mmin = [get_int(kv, "melee_min") for kv in forms if get_int(kv, "melee_min") is not None]
        mmin = [v for v in mmin if v >= 0]
        if rmin:
            worst = min(rmin)
            if worst < RANGED_SAFE:
                check(BAD, f"远程兵贴脸（冲进敌堆）：总攻期最近距离最小 {worst} 格"
                           f"（安全阈值 {RANGED_SAFE} 格）",
                      f"采样 {len(forms)} 次，远程最小距离序列（前20）: {rmin[:20]}")
            else:
                check(OK, f"远程兵保持了攻击距离：最小 {worst} 格（阈值 {RANGED_SAFE}）",
                      f"采样 {len(forms)} 次，最小距离序列（前20）: {rmin[:20]}")
        else:
            print("[--] 阵型采样中无远程兵数据")
        if mmin:
            print(f"        近战兵到最近敌最小距离: {min(mmin)} 格（采样 {len(mmin)} 次）")
    else:
        print("[--] 无 formation 采样（总攻期视野内可能没有敌人，见下）")

    # ---------- 检查 7: 总攻时视野内敌人 ----------
    if "offense_start" in by:
        kv = by["offense_start"][0]
        ea, eb = get_int(kv, "enemy_army", default=0), get_int(kv, "enemy_build", default=0)
        if ea == 0 and eb == 0:
            check(WARN, "总攻开始时视野内 0 个敌兵 / 0 个敌建筑 ——"
                        " 若此时祭司不转化，根因是**没侦察到敌人**，不是转化逻辑",
                  f"offense_start: {kv}")
        else:
            check(OK, f"总攻开始时视野内有敌兵 {ea} / 敌建筑 {eb}")

    # ---------- 检查 9: 马厩 / 侦察兵产出 ----------
    section("马厩 / 侦察兵产出")
    stable = by.get("stable_built", [])
    trained = by.get("scout_trained", [])
    if stable:
        check(OK, f"马厩已建成：frame {get_int(stable[0], 'frame')}")
    else:
        check(BAD, "马厩从未建成（stable_built 缺失）")
    if trained:
        check(OK, f"侦察兵已训出：frame {get_int(trained[0], 'frame')}")
    else:
        check(BAD, "侦察兵从未训出（scout_trained 缺失）")

    # ---------- 检查 8: 侦察兵探路 ----------
    section("侦察兵探路")
    found = by.get("siege_found", [])
    path_start = by.get("scout_path_start", [])
    sdeaths = by.get("scout_died", [])
    kv = None
    for f in found:               # 优先取带坐标的那条（探针版）；里程碑版无坐标
        if "siege_dr" in f:
            kv = f
            break
    if kv is None and found:
        kv = found[0]
    if kv:
        fr = get_int(kv, "frame")
        dur = ""
        if path_start:
            ps = get_int(path_start[0], "frame")
            if ps is not None and fr is not None:
                dur = f"（探路开始 frame {ps}，耗时 {fr - ps} 帧）"
        check(OK, f"侦察兵成功探到敌方攻城厂：frame {fr} {dur}",
              f"厂区位于 ({get_int(kv, 'siege_dr')},{get_int(kv, 'siege_ur')})")
    else:
        check(BAD, "侦察兵从未探到敌方攻城厂（探路失败）")
        if sdeaths:
            check(WARN, f"侦察兵阵亡 {len(sdeaths)} 次",
                  "\n".join(f"frame {get_int(kv, 'frame')}" for kv in sdeaths))
        else:
            print("        侦察兵全程存活 → 失败原因不是阵亡，而是路线卡死或出发时机问题")

    # 探路期位置检测：①原地(长时间不动) ②打转(绕圈，路程大但净位移小)
    # 只在"探路开始(scout_path_start)"之后判定，避免把出发前的"待命在家"误判为卡死
    ps_frame = get_int(path_start[0], "frame") if path_start else 0
    poses = sorted(by.get("scout_pos", []), key=lambda kv: get_int(kv, "frame") or 0)
    pathing_poses = [kv for kv in poses if (get_int(kv, "frame") or 0) > ps_frame
                     and not get_int(kv, "known", default=0)]
    if pathing_poses:
        # ① 原地：连续采样间隔 ≥2400 帧、位置移动 <2 格
        stuck_seg = 0
        stuck_detail = []
        for i in range(1, len(pathing_poses)):
            f0 = get_int(pathing_poses[i - 1], "frame") or 0
            f1 = get_int(pathing_poses[i], "frame") or 0
            x0, y0 = get_int(pathing_poses[i - 1], "dr", default=0), get_int(pathing_poses[i - 1], "ur", default=0)
            x1, y1 = get_int(pathing_poses[i], "dr", default=0), get_int(pathing_poses[i], "ur", default=0)
            if f1 - f0 >= 2400 and math.hypot(x1 - x0, y1 - y0) < 2:
                stuck_seg += 1
                stuck_detail.append(f"frame {f0}~{f1} 停在 ({x0},{y0})")
        if stuck_seg:
            check(BAD, f"侦察兵疑似原地不动 {stuck_seg} 段（位置 ≥2400 帧不变）",
                  "\n".join(stuck_detail[:8]))
        else:
            check(OK, "侦察兵无原地停留（探路期位置一直在变）")

        # ② 打转：探路期总路程 vs 净位移——路程大、净位移小 = 绕圈
        if len(pathing_poses) >= 4:
            xs = [get_int(kv, "dr", default=0) for kv in pathing_poses]
            ys = [get_int(kv, "ur", default=0) for kv in pathing_poses]
            path = sum(math.hypot(xs[i] - xs[i - 1], ys[i] - ys[i - 1]) for i in range(1, len(xs)))
            net = math.hypot(xs[-1] - xs[0], ys[-1] - ys[0])
            span = (get_int(pathing_poses[-1], "frame") or 0) - (get_int(pathing_poses[0], "frame") or 0)
            if span >= 2400 and path >= 8 and net <= 4:
                check(BAD, f"侦察兵疑似打转：探路期路程 {int(path)} 格，净位移仅 {int(net)} 格（绕圈）",
                      f"span {span} 帧，{len(pathing_poses)} 个采样")
            else:
                check(OK, f"侦察兵无打转：路程 {int(path)} 格 / 净位移 {int(net)} 格（span {span} 帧）")
        else:
            print("[--] 探路期位置采样不足，跳过打转检测")
    else:
        print("[--] 探路期无有效位置采样（可能出发太晚/很快探到厂区/很快阵亡）")

    # ---------- 事件计数 ----------
    section("事件计数")
    for name in sorted(by):
        print(f"  {name:<24} {len(by[name])}")


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    if not args:
        print(__doc__)
        sys.exit(1)

    def opt(name, default):
        for a in sys.argv[1:]:
            if a.startswith("--" + name + "="):
                return int(a.split("=", 1)[1])
        return default

    path = args[0]
    WAVE3 = opt("wave3", 21000)
    RANGED_SAFE = opt("ranged-min", 8)   # 远程兵到最近敌的安全距离阈值(格)
    OSC_LIMIT = opt("osc", 8)            # 折返次数告警阈值

    try:
        events = parse_log(path)
    except FileNotFoundError:
        print(f"找不到日志文件: {path}")
        sys.exit(1)

    # 按 session_start 切分成多次运行（支持把好几局日志 append 到同一个文件）
    runs = []
    cur = []
    for name, kv in events:
        if name == "session_start" and cur:
            runs.append(cur)
            cur = []
        cur.append((name, kv))
    if cur:
        runs.append(cur)

    if len(runs) <= 1:
        analyze_run(path, events, WAVE3, RANGED_SAFE, OSC_LIMIT)
    else:
        # 多局模式：先打印逐局汇总对比表，再逐局打印详细报告
        print("=" * 58)
        print(f"检测到 {len(runs)} 次运行（同一日志文件 {path}）")
        print("=" * 58)
        hdr = f"{'局':<3}{'开始帧':<8}{'结束帧':<9}{'祭司':<7}{'探到厂区':<9}{'转化':<5}{'第三波后建塔':<9}{'马厩':<5}{'侦察兵':<6}"
        print(hdr)
        print("-" * len(hdr))
        for i, r in enumerate(runs, 1):
            rby = defaultdict(list)
            for n, kv in r:
                rby[n].append(kv)
            frs = [get_int(kv, "frame") for _, kv in r if get_int(kv, "frame") is not None]
            s0, s1 = (min(frs), max(frs)) if frs else ("?", "?")
            priest = "阵亡" if "priest_died" in rby else "存活"
            found = "是" if "siege_found" in rby else "否"
            conv = len(rby.get("convert_pick", []))
            tower_after = len([kv for kv in rby.get("tower_build", [])
                               if (get_int(kv, "frame") or 0) > WAVE3])
            stable_ok = "是" if "stable_built" in rby else "否"
            scout_ok = "是" if "scout_trained" in rby else "否"
            print(f"{i:<3}{str(s0):<8}{str(s1):<9}{priest:<7}{found:<9}{conv:<5}{tower_after:<9}{stable_ok:<5}{scout_ok:<6}")

        for i, r in enumerate(runs, 1):
            analyze_run(f"第 {i} 局（共 {len(runs)} 局）", r, WAVE3, RANGED_SAFE, OSC_LIMIT)

        print("\n" + "=" * 58)
        print("提示")
        print("  * 多局模式：先看上面的逐局汇总表对比，再逐局看详细报告。")
        print("  * 想看原始明细：grep 'priest_move' / 'tower_build' / 'scout_pos'。")
        print("=" * 58)


if __name__ == "__main__":
    main()
