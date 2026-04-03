[English Version](README_en.md)

# 基于Lean实现的形式化杀戮尖塔核心逻辑引擎

- 本项目通过Lean实现了一个杀戮尖塔核心游戏的引擎，包括关键的抽牌，弃牌，洗牌逻辑，各角色状态机，90+卡牌（包括能力牌）
- 本项目是可拓展的，在所有已经定义的卡牌中，都可以自由组合卡牌，用python脚本构造新的proposition来进行证明
- 同时，本项目对一系列案例combo提供了证明样本
- 核心证明思路：构造一个循环，从一个手牌堆，抽牌堆，弃牌堆状态出发，可以在打出正数伤害的情况下回到当前状态


## 证明等级

**Level 1 — 存在性证明：**
假设玩家是幸运的，一定能抽到自己想要的牌，只需证明存在某种洗牌顺序使连击循环。
- LLM 提供：`setupTrace`（准备阶段操作序列）、`loopTrace`（循环操作序列）、`stateA`、`stateB`（循环前后状态）
- Lean 通过 `native_decide` 验证：准备阶段到达 stateA，循环到达 stateB，状态匹配，伤害增加
- 这种证明较为简单，实际上只需要提供一个trace即可，不需要复杂的证明技术
- 命题：`InfiniteCombo`

**Level 2 — 对抗对手控制的洗牌：** 玩家可以在前几个回合进行启动（假设幸运），但在无限循环回合必须处理所有洗牌情况（由 `ShuffleOracle` 控制）。
- `native_decide` 仅允许用于引擎计算辅助引理，不允许出现在主证明体中
- 三个证明目标（强度递减）：

| 强度 | 命题 | 量词结构 | 含义 |
|------|------|---------|------|
| 最强 | `GuaranteedInfiniteCombo` | `∀oracle ∃trace, sameModAccum` | 周期1循环：状态精确回归 |
| 中等 | `RobustInfinite` | `∀oracle ∃strategy ∀N ∃K, damage > N` | 固定策略击杀任意血量 |
| 最弱 | `UnboundedDamage` | `∀oracle ∀N ∃trace, damage > N` | 每个血量目标对应一个策略 |

- `RobustInfinite → UnboundedDamage` 已证明。`GuaranteedInfiniteCombo → RobustInfinite` 已声明（sorry）。

## 项目结构

```
StSVerify/
  Engine.lean                — 游戏引擎：状态、效果、动作、execute、executeL2
  EngineHelperLemmas.lean    — 一些提前证明好的可以辅助证明的helper
  CardId.lean                — 93 张卡牌名称全局枚举
  Cards/                     — 每张卡牌一个定义文件（93 个文件）
  CardDB.lean                — CardName → CardDef 查找表
  Demo.lean                  — Level 1 证明示例（猎手 5 卡连击）
  CombosTemplateL1/          — Level 1 模板（12 个连击，含 sorry）
  CombosTemplateL2/          — Level 2 模板（12 个连击，含 sorry）
  CombosLevel1Solution/      — Level 1 参考解答（12/12 已验证）
  CombosLevel2Solution/      — Level 2 参考解答（11/12 已验证，1 开放挑战）
data/
  combos_v2.jsonl            — 连击定义（卡牌、敌人状态、效果）
generate_cards.py            — 生成 Cards/*.lean 和 CardDB.lean
generate_templates.py        — 从 combos_v2.jsonl 生成模板文件
```

## 连击列表（12 个）

| 连击 | 卡牌数 | 角色 | 洗牌复杂度 | L1 | L2 |
|------|--------|------|-----------|----|----|
| 飞踢消耗精简无限 | 11 | 铁甲战士 | 单卡洗牌（确定性） | ✅ | ✅ |
| 腐化消耗精简+飞踢 | 13 | 铁甲战士 | 单卡洗牌（确定性） | ✅ | ✅ |
| 足跟勾+消耗精简 | 10 | 静默猎手 | 单卡洗牌（确定性） | ✅ | ✅ |
| 流线型+全息影像+精简 | 11 | 故障机器人 | 循环无洗牌 | ✅ | ✅ |
| 双杂技+战术大师 | 12 | 静默猎手 | 4 个洗牌点 | ✅ | ✅ |
| 真言/神格混合无限 | 13 | 观者 | 6 种排列 | ✅ | ✅ |
| 标准沙雕无限 | 12 | 观者 | 4 种情况（2×2） | ✅ | ✅ |
| 钢铁风暴（4卡） | 4 | 静默猎手 | 12 种排列（2×6） | ✅ | ✅ |
| 钢铁风暴+2准备（5卡） | 5 | 静默猎手 | 48 种情况（24×2） | ✅ | ✅ |
| 钢铁风暴+3准备（6卡） | 6 | 静默猎手 | 720+种情况，级联洗牌 | ✅ | ⬚ |
| 钢铁风暴+打击（5卡） | 5 | 静默猎手 | 对手可困住准备+ | ✅ | ✅ |
| 发泄+不惧妖邪双输出 | 11 | 观者 | 48 种情况（24×2） | ✅ | ✅ |

- **L1**：12/12 已证明（单回合内循环，无需结束回合）
- **L2**：11/12 `GuaranteedInfiniteCombo` 已证明
   - 钢铁风暴+3准备：非 `GuaranteedInfiniteCombo`（6卡牌组，对手可困住本能反应+导致周期1循环断裂）。猜测为 `UnboundedDamage`（玩家可自适应地利用准备+恢复本能反应+）。**开放挑战——最难的benchmark，无参考解答** — ⬚

## L2 证明技术

较难的连击（钢铁风暴+打击、发泄+不惧妖邪、钢铁风暴 2/3 准备）使用 **drawCondBool 桥接** 模式：

1. 定义 `drawCondBool fo p1 p2 si s trace : Bool`——使用固定 oracle 逐步执行，在每个抽牌步骤检查抽牌堆是否非空或是否在已知洗牌点
2. 通过单次 `native_decide` 验证所有排列组合的 `drawCondBool`（具体引擎计算）
3. 证明 `drawCondBool_bridge`：如果检查通过且真实 oracle 在洗牌点一致，则 `executeL2` 给出相同结果（通过归纳法和 `stepL2_oracle_cond` 证明）
4. 主定理结合桥接与排列完备性

较简单的连击使用直接步骤链证明（`exL2_cons` + `perm_singleton_eq`/`perm_3_cases`）。

### 最难挑战：钢铁风暴+3准备（6卡）

**连击**：钢铁风暴+ + 战术大师+ + 本能反应+ + 3x早有准备+（6张卡）

**为什么难**：与所有其他连击不同，6卡牌组产生级联洗牌交互，无法形成简单的周期1循环：
- 循环后：本能反应+的抽3从子洗牌中抽2留1，导致1张牌滞留在抽牌堆
- 状态从（手牌=6，抽牌堆=0）变为（手牌=5，抽牌堆=1）——`sameModAccum` 失败
- 对手可以选择困住本能反应+本身，导致下一轮抽3触发断裂
- 当本能反应+滞留在抽牌堆且弃牌堆为空时，准备+无法恢复它（抽牌失败）

**证明目标**：`UnboundedDamage`（非 `GuaranteedInfiniteCombo`）

**猜测策略**：玩家可自适应地打出无限伤害：
1. 当对手不利时，保留本能反应+在手牌中（不通过准备+弃掉）
2. 手牌中有本能反应+时打出钢铁风暴 → stormOfSteel弃掉本能反应+ → 触发抽3
3. 利用3张准备+循环牌组，恢复钢铁风暴进行下一轮伤害
4. 每次钢铁风暴至少产生1把匕首 = 4点伤害

**状态**：开放挑战——无参考解答。需要证明复杂的多轮自适应策略。

### 示例分析（已证明）：钢铁风暴+2准备（5卡）

2准备变体 IS `GuaranteedInfiniteCombo`。5张卡，2个洗牌点（Oracle 0: 120种排列，Oracle 1: 6种排列 = 共720种），使用 drawCondBool 桥接模式证明：

1. **计算验证层**：`native_decide` 验证全部 720 种排列组合
2. **Oracle 桥接层**：通过对 trace 归纳证明 oracle 等价性（`stepL2_oracle_cond`）
3. **排列完备性层**：数学 case analysis 证明 `List.Perm l pile → l ∈ allPerms`（Nodup + 元素成员性）
4. **主定理层**：引入 oracle，组装桥接与验证。**主证明体中无 `native_decide`**

## 安全性检查

评估框架检查 LLM 提交的代码：
- `sorry` — 不完整证明
- `axiom` — 虚假假设
- `unsafe` — 绕过内核
- `instance` — 不健全的可判定性实例
- 框架函数重定义
- 未授权的导入
- L2：`native_decide` 不在主证明体中（仅限引擎辅助引理）

## 命令

```bash
# 构建并验证所有证明
cd lean_framework && export PATH="$HOME/.elan/bin:$PATH" && lake build

# 验证单个解答
lake env lean StSVerify/CombosLevel1Solution/ComboDropkickExhaust.lean
lake env lean StSVerify/CombosLevel2Solution/ComboDropkickExhaust.lean

# 从连击数据生成模板
python generate_templates.py
```

## 开放问题

形式化过程中产生了若干开放问题（扩展定义见 `ExtendedTargets.lean`）：

1. **[钢铁风暴+, 战术大师+, 本能反应+, 早有准备+×3] 能否打出无限伤害？**
   6卡牌组中，对手可以通过洗牌将本能反应+困在抽牌堆底部，使得"抽3"触发断裂，周期1循环不成立。但玩家或许可以通过自适应策略（保留本能反应+在手牌、利用3张早有准备+循环牌组）持续输出伤害。目前无参考解答。

2. **预知洗牌结果是否严格增强玩家能力？**
   我们的 `UnboundedDamage` 定义允许玩家在选择操作前看到全部洗牌结果（离线优化）。`OnlineUnboundedDamage` 要求玩家只能根据已经发生的洗牌结果做决策（在线策略，对应真实游戏）。是否存在某个连击满足前者但不满足后者？

3. **周期1循环 → 固定策略（`GuaranteedInfiniteCombo → RobustInfinite`）**
   如果一个连击能在任意洗牌下循环一次回到原状态，能否将其重复N次构成一个固定的无限操作序列？直觉显然，但形式证明需要"状态等价的引擎行为相同"这一模拟定理。目前为 sorry。

## 已知限制

### 未实现
- **遗物** — 日晷、永不停歇的陀螺等。10 个遗物连击已从数据集中排除。
- **保留** — 卡牌跨回合保留（奇迹、洞察、冥想+）。
- **连发/双击** — "接下来 N 个技能/攻击打出两次"。
- **X 费卡** — 可变费用未建模。
- **HP 追踪** — 引擎不追踪生命值或死亡。
- **敌人行动** — `endTurn` 不模拟敌人攻击或减益衰减。
- **易伤/虚弱衰减** — 减益保持不变（真实游戏：每回合减少 1）。
- **力量** — 未追踪。

### 简化
- **敌人状态固定** — 易伤/虚弱作为初始参数设定，不衰减。
- **格挡每回合重置** — 壁垒（格挡保留）未建模。
- **充能球被动** — 充能球可引导/唤出，但不触发每回合效果。
- **伤害取整** — 易伤 1.5 倍使用整数除法（与游戏一致）。
