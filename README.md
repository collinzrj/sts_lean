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

**Level 2 — 保证循环：** 玩家可以在前几个回合进行启动，为了降低复杂度，我们假设在前几个启动回合，玩家是幸运的，但是在最后达到无限的回合，必须能够处理所有情况
- 准备阶段使用 Level 1（幸运抽牌），循环通过 `ShuffleOracle` 处理所有洗牌
- LLM 必须证明 `∀ oracle, validOracle oracle → ∃ loopTrace stateB, ...`
  - 即，在所有需要洗牌的时候，对于任何一种洗牌的排列，都可以找到某种方案打出无限
- `native_decide` 仅允许用于引擎计算辅助引理（单步执行、状态比较）
- `native_decide` 不允许出现在主证明体中——oracle 量化必须使用真正的证明策略
  - 这是一个heuristic，用来鼓励模型减少穷举
- 命题：`GuaranteedInfiniteCombo`

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
  CombosLevel2Solution/      — Level 2 参考解答（12/12 已验证）
data/
  combos_v2.jsonl            — 连击定义（卡牌、敌人状态、效果）
generate_cards.py            — 生成 Cards/*.lean 和 CardDB.lean
generate_templates.py        — 从 combos_v2.jsonl 生成模板文件
```

## 连击列表（12 个）

| 连击 | 卡牌数 | 角色 | 洗牌复杂度 |
|------|--------|------|-----------|
| 飞踢消耗精简无限 | 11 | 铁甲战士 | 单卡洗牌（确定性） |
| 腐化消耗精简+飞踢 | 13 | 铁甲战士 | 单卡洗牌（确定性） |
| 足跟勾+消耗精简 | 10 | 静默猎手 | 单卡洗牌（确定性） |
| 流线型+全息影像+精简 | 11 | 故障机器人 | 循环无洗牌 |
| 双杂技+战术大师 | 12 | 静默猎手 | 4 个洗牌点 |
| 真言/神格混合无限 | 13 | 观者 | 6 种排列 |
| 标准沙雕无限 | 12 | 观者 | 4 种情况（2×2） |
| 钢铁风暴（4卡） | 4 | 静默猎手 | 6 种排列 |
| 钢铁风暴+2准备（5卡） | 5 | 静默猎手 | 3 个洗牌点 |
| 钢铁风暴+3准备（6卡） | 6 | 静默猎手 | 3 个洗牌点 |
| 钢铁风暴+打击（5卡） | 5 | 静默猎手 | 576 种情况（24×24） |
| 发泄+不惧妖邪双输出 | 11 | 观者 | 48 种情况（24×2） |

## L2 证明技术

较难的连击（钢铁风暴+打击、发泄+不惧妖邪、钢铁风暴 2/3 准备）使用 **drawCondBool 桥接** 模式：

1. 定义 `drawCondBool fo p1 p2 si s trace : Bool`——使用固定 oracle 逐步执行，在每个抽牌步骤检查抽牌堆是否非空或是否在已知洗牌点
2. 通过单次 `native_decide` 验证所有排列组合的 `drawCondBool`（具体引擎计算）
3. 证明 `drawCondBool_bridge`：如果检查通过且真实 oracle 在洗牌点一致，则 `executeL2` 给出相同结果（通过归纳法和 `stepL2_oracle_cond` 证明）
4. 主定理结合桥接与排列完备性

较简单的连击使用直接步骤链证明（`exL2_cons` + `perm_singleton_eq`/`perm_3_cases`）。

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
