# Lean Artifact Inventory Audit

Механическая инвентаризация всех Lean-артефактов репозитория.
Цель: отделить проверяемое содержание от бухгалтерии и от пустых деклараций.

Дата: 2026-07-27
Метод: статический анализ 127 файлов `Proofs/**/*.lean` + сверка с `.lake/build`.

**Ограничение метода:** в среде аудита нет `lake`/`lean`, поэтому компиляция не
запускалась. Статус компиляции выведен из наличия и времени `.olean` файлов.
Все выводы о содержании получены чтением исходников, а не проверкой компилятором.

**Обновление 2026-07-27, машина с Lean 4.29.0:** всё, что ниже помечено как
непроверенное, прогнано. Раздел 10 содержит результат прогона и список мест,
где аудит оказался неверен. Числа в разделах 1–9 оставлены в том виде, в
котором были получены статически; там, где прогон их опроверг, стоит ссылка
на раздел 10.

---

## 1. Сводные числа

| Метрика | Значение |
|---|---|
| Lean-файлов в `Proofs/` | 127 |
| Всего теорем/лемм | 922 |
| Доказаны цепочкой `trivial`/`rfl`/`And.intro` | 169 (18%) |
| Присваиваний `:= True` в полях структур | 405 |
| Голых полей `: Prop` в структурах | 517 |
| Аксиом | 6 |
| Файлов, импортирующих Mathlib | 19 |
| Строк кода всего | 25 028 |
| **Строк с настоящим математическим содержанием** | **447 (1.8%)** |

### Статус компиляции

| Состояние | Файлов |
|---|---|
| Скомпилировано и свежо | 87 |
| Устарело (исходник новее `.olean`) | 27 |
| **Никогда не компилировалось** | **15** |

Среди никогда не компилировавшихся — `V7LocalTomography.lean` и
`V7BoundedCorrelations.lean`, на которые секция 175 ссылается как на `derived`.

> **Опровергнуто прогоном (раздел 10.1).** Причина не в файлах, а в
> `lakefile.lean`: в нём не было `@[default_target]`, поэтому `lake build`
> печатал «Build completed successfully (0 jobs)» и не компилировал ничего.
> 12 из 15 файлов вообще не входили ни в одну цель сборки, но компилируются
> без ошибок по отдельности. Реально сломанных файлов было 2, а не 15, и
> `V7LocalTomography.lean` в их число не входит.

---

## 2. Что является настоящей математикой

Семь файлов содержат проверяемое математическое содержание. Все, кроме
последнего, скомпилированы и не содержат аксиом.

| Файл | Строк | Что доказано |
|---|---|---|
| `ExclusivityAdditivityProof.lean` | 92 | аддитивность меры на непересекающихся множествах при нулевом кросс-члене |
| `CoarseGrainingConsistencyProof.lean` | 46 | то же для трёх множеств |
| `OperationalEquivalenceProbabilityProof.lean` | 46 | инвариантность меры относительно биекции, сохраняющей `W` и `Γ` |
| `ContextNormalizationProof.lean` | 41 | из PSD-условия следует неотрицательность меры |
| `V7PositiveGeometryGeneral.lean` | 100 | полная характеризация PSD для вещественной формы 2×2 |
| `V7PositiveGeometryConcrete.lean` | 79 | конкретные примеры и контрпримеры 2×2 |
| `V7PositiveGeometryTwoAlternatives.lean` | 43 | содержит 1 аксиому; **никогда не компилировался** |

Доказательства корректны и нетривиальны в смысле формализации. Замечания по
существу — в разделе 4.

> **Уточнено прогоном (раздел 10.2).** Последняя строка не относится к
> «настоящей математике». `V7PositiveGeometryTwoAlternatives.lean` не
> компилировался из-за ошибки типов (`def Real := Rat` нередуцируем для поиска
> инстансов), работает не над ℝ, а над `Rat`, и его единственная «теорема»
> `positiveGeometry2` — это его собственная аксиома `facticizationNonneg`,
> переписанная под другим именем. Файлов с настоящим содержанием — 6, не 7.

---

## 3. Построчная сверка таблицы 175.2

Секция `175-primitive-base-completeness-status.md` содержит таблицу
«What is proved (Lean-verified)». Проверка каждой строки:

| Строка 175 | Заявленный статус | Фактическое состояние |
|---|---|---|
| B0 satisfied without F (countermodel) | `formal proof` | **доказывает не то**: модель B0 вырождена (`D := True`, `C`/`O`/`I` не участвуют), а `F` определена как `∀ c1 c2 a, R c2 a → R c1 a`, то есть как отрицание контекстуальности — утверждение, которое теория обязана отвергать |
| F → a ≥ 0 (2×2) | `linarith proof` | **верно** |
| F → c ≥ 0 (2×2) | `linarith proof` | **верно** |
| F → a+2b+c ≥ 0 | `linarith proof` | **верно** |
| F → a−2b+c ≥ 0 | `linarith proof` | **верно** |
| F → ac ≥ b² (2×2) | `axiom (strategy known)` | **занижено**: полностью доказано в `det_nonneg` через разбор случаев и `nlinarith`; аксиомы в файле нет |
| Identity form is PSD | `nlinarith proof` | **верно** |
| [[1,2],[2,1]] rejected by F | `counterexample` | **верно** |
| [[2,1,1,2]] is PSD | `proved` | **верно** |
| [[1,3,1]] rejected by F | `counterexample` | **верно** |
| [[1,0.5,1]] is PSD | `proved` | **верно** |
| Product exhaustion from B0 | `derived` | **пусто**: все теоремы вида `... → True := trivial` |
| Local tomography from B0 | `derived` | **пусто**: `True := trivial`; файл никогда не компилировался |
| Bounded correlations from B0+F | `derived` | **пусто**: `theorem tsirelsonLike : True := trivial`, `theorem noSignalling : True := trivial`, плюс `axiom facticizationStability : True`; файл никогда не компилировался |
| Hilbert carrier selection | `conditional` | **пусто**: три посылки — `True := trivial`, плюс `axiom facticizationNonneg` |
| Born rule derivation | `conditional` | **пусто**: три посылки — `True := trivial`, плюс `axiom quadraticFromCarrier : True` |
| Metric geometry projection | `conditional` | **пусто**: три посылки — `True := trivial` |
| D_G = 4 NOT derivable | `analysis` | **пусто**: файл целиком из `Prop := True -- placeholder`, `theorem : True := trivial`; отрицательный результат не доказан |

Итог: из 18 строк **9 верны** (положительная геометрия 2×2), **1 занижена**,
**8 не подтверждены содержанием файлов**.

Пустые строки сосредоточены ровно там, где делаются содержательные утверждения
о физике. Верные строки — там, где утверждается элементарная линейная алгебра.

---

## 4. Замечание по существу к настоящим доказательствам

Четыре файла с реальным содержанием — `ExclusivityAdditivityProof`,
`CoarseGrainingConsistencyProof`, `OperationalEquivalenceProbabilityProof`,
`ContextNormalizationProof` — стартуют с сигнатуры:

```lean
variable (W : H → ℂ)
variable (Γ : H → H → ℂ)
noncomputable def actualizationMeasure (A : Finset H) : ℂ :=
  ∑ h ∈ A, ∑ h' ∈ A, W h * star (W h') * Γ h h'
```

Это полуторалинейная форма на комплексном векторном пространстве с эрмитовым
ядром, то есть гильбертова структура без названия.

Заголовки этих файлов при этом объявляют:

```
Forbidden imports: born_rule, kolmogorov_axioms_assumed, hilbert_space
```

Секция `01-primitives.md` сама помечает `W : H → ℂ` как
`QM carrier import / readout scaffold`. То есть репозиторий знает, что `W` — это
импорт, но файлы, построенные на `W`, декларируют его запрещённым.

Что фактически доказано в этих четырёх файлах: полуторалинейная форма аддитивна
на непересекающихся множествах при нулевом кросс-члене, неотрицательна при
PSD-ядре, и инвариантна относительно биекций, сохраняющих данные. Это верные и
стандартные утверждения о предположенной структуре. Они не выводят структуру.

Аналогично `V7PositiveGeometryGeneral.lean`: доказана стандартная характеризация
PSD для формы 2×2. Формализация корректна, математика элементарна, утверждения о
мире в ней нет.

---

## 5. Разделение всего корпуса

| Категория | Файлов | Строк | Доля |
|---|---|---|---|
| Настоящая математика (о предположенной структуре) | 7 | 447 | 1.8% |
| Бухгалтерия и governance (`MetaLang/V8*`, реестры, ledger'ы) | ~60 | ~14 000 | 56% |
| Пустые декларации (`Prop := True`, `theorem : True := trivial`) | ~60 | ~10 500 | 42% |

Файлы категории «бухгалтерия» содержат настоящие Lean-доказательства — `decide`,
`simp`, разбор случаев по перечислениям — но доказывают они свойства собственных
структур данных репозитория: длину списка, непротиворечивость статуса, полноту
словаря. Как инфраструктура дисциплины заявлений они честны. К физике отношения
не имеют.

---

## 6. Выводы

1. Доказано: элементарная линейная алгебра положительных форм 2×2 и базовые
   свойства полуторалинейной меры. Всё — о предположенной комплексной структуре.

2. Не доказано ничего из того, ради чего теория существует: ни product
   exhaustion, ни local tomography, ни bounded correlations, ни выбор носителя,
   ни правило Борна, ни метрическая проекция, ни невыводимость `D_G = 4`.
   Соответствующие файлы содержат `True := trivial`.

3. Одно занижение: `ac ≥ b²` доказано, а в 175 числится аксиомой. Таблица
   отстала от кода.

4. Настоящая математика построена на импорте, который её же заголовки объявляют
   запрещённым.

5. 15 файлов никогда не компилировались, 27 устарели. Два из
   некомпилировавшихся цитируются как `derived`.

## 7. Почему сторож не сработал

`README.md` и `PUBLIC_CLAIM_SHEET.md` (п. 23) утверждают, что тело каждого из
пяти `proved` артефактов сканируется на запрещённые символы, «so that none of
them silently imports Hilbert-space, Born-rule, positive-operator, unitary,
tensor, or projective-Hilbert machinery».

Сканер существует и работает: `scripts/evaluate_full_qm_proof_closure.py`,
таблица `FORBIDDEN_IMPORT_BODY_SYMBOLS`. Он ищет в теле файла имена типов
Mathlib:

```python
"hilbert_space": ("InnerProductSpace", "Mathlib.Analysis.InnerProductSpace", "HilbertSpace"),
"projective_hilbert_space": ("Projectivization", ...),
```

Пять артефактов проходят проверку, потому что не используют ни одного из этих
имён. Они собирают ту же структуру вручную:

```lean
variable (W : H → ℂ)
variable (Γ : H → H → ℂ)
∑ h ∈ A, ∑ h' ∈ A, W h * star (W h') * Γ h h'
```

`ℂ`, `star` и `Finset.sum` в списке запрещённых символов отсутствуют. Так же
проходит и PSD: `ContextNormalizationProof.lean` определяет

```lean
def FacticizationStabilityReal (Γ : H → H → ℝ) : Prop :=
  ∀ (v : H → ℝ), ∑ h, ∑ h', v h * v h' * Γ h h' ≥ 0
```

то есть положительную полуопределённость по определению, а сканер ищет символ
`PositiveSemidefinite`.

Отдельно: manifest-уровневый сторож в `theory_verifier/core.py`
(`IDT_PRIMITIVE_CORE_FORBIDDEN_REFS`) включает строки `"W"`, `"Gamma_I"`,
`"complex_amplitude_carrier"`, `"quadratic_actualization_measure"` — но
проверяет их так:

```python
scanned = (primitive_id, *laws, *allowed_dependencies)
forbidden_ref_hits = tuple(sorted(r for r in forbidden_refs if r in scanned))
```

`scanned` — кортеж строк из манифеста, а не содержимое Lean-файла. Проверка
сравнивает декларации манифеста сами с собой и Lean-исходников не читает.

Итог: запрет обходится не злым умыслом, а тем, что сторож ловит имена
библиотечных типов, а не математическую структуру. Ручная реализация того же
объекта невидима.

Оговорка: сканеры прочитаны как код, но не запущены (в среде аудита нет Python-
окружения проекта и Lean). Вывод следует из текста `FORBIDDEN_IMPORT_BODY_SYMBOLS`
и `primitive_core_witnesses`, а не из наблюдённого прогона.

Что чинить: добавить в body-скан обнаружение полуторалинейного паттерна
(`star` + `ℂ` + двойная сумма) и определений вида `∀ v, ∑∑ v·v·Γ ≥ 0`, либо —
надёжнее — требовать от артефактов, претендующих на carrier-neutrality, явной
декларации «комплексные скаляры не используются», проверяемой отдельно.

## 8. Что сделано по результатам аудита

### 8.1. Статусы приведены в соответствие с кодом

`sections/175-primitive-base-completeness-status.md` переписана: 8 строк
понижены, 1 повышена, разделы 175.3–175.6 исправлены, четыре живых определения
базы записаны как открытое противоречие. Коммит `7d63268`.

### 8.2. Пустые артефакты помечены

Введён точный критерий: теорема пуста, если её заключение — `True`, напрямую или
через `def X : Prop := True`. Как она доказана, значения не имеет.

По этому критерию: **32 пустые теоремы из 922, в 8 файлах**.

| Файл | Пустых / всего |
|---|---|
| `V7BornRuleDerivation.lean` | 4 / 4 |
| `V7HilbertCarrierSelection.lean` | 4 / 4 |
| `V7MetricGeometryProjection.lean` | 4 / 4 |
| `V7BoundedCorrelations.lean` | 3 / 3 |
| `V7DimensionAnalysis.lean` | 3 / 3 |
| `V7LocalTomography.lean` | 3 / 3 |
| `V7ProductContextExhaustion.lean` | 3 / 3 |
| `V8QmResearchTaskLedger.lean` | 8 / 61 |

Каждый снабжён заголовочным маркером `EMPTY_PLACEHOLDER`. Введён
`scripts/check_vacuous_theorems.py`, который падает, если пустая теорема не
объявлена — и симметрично, если маркер стоит на файле без пустых теорем, чтобы
маркер не превратился в украшение.

Заметим, что 18% «тривиальных доказательств» из раздела 1 — метрика грубая и
завышающая: `rfl` и `decide` часто доказывают содержательные утверждения о
перечислениях. Критерий «заключение есть `True`» точнее и даёт 3.5%.

### 8.3. Сторож импортов чинён

В `scripts/evaluate_full_qm_proof_closure.py` добавлены два слоя:

1. `FORBIDDEN_IMPORT_BODY_PATTERNS` — структурные паттерны вместо имён типов:
   - `SESQUILINEAR` — совместное присутствие `ℂ`, `star` и двойной суммы;
   - `PSD_FORM` — определение вида `∀ v, ∑ ∑ v·v·Γ ≥ 0`.
   Паттерны конъюнктивны: одиночный `star` или одна сумма не срабатывают.
2. `_expand_local_imports` — скан идёт по телу артефакта вместе с телами
   локальных модулей `Proofs.*`, которые он импортирует, с защитой от циклов.

Результат на пяти `proved`-карточках:

| Карточка | До | После |
|---|---|---|
| `context_normalization` | чисто | чисто (вещественная, комплексного носителя нет) |
| `exclusivity_additivity` | чисто | **flagged: hilbert_space** |
| `coarse_graining_consistency` | чисто | **flagged: hilbert_space** |
| `operational_equivalence_probability` | чисто | **flagged: hilbert_space** (через локальный импорт) |
| `projective_action` | чисто | чисто |

Тест `test_five_machine_checked_cards_pass_body_scan` утверждал ровно то, что
аудит опроверг, и был переписан: три карточки теперь обязаны помечаться, две
обязаны оставаться чистыми. Снять пометку можно только перестроив
доказательства без комплексных амплитуд, но не ослаблением скана. Добавлено 8
модульных тестов на новый слой.

**Следствие, которое нужно проверить у себя:** `evaluate_full_qm_proof_closure.py`
требует `lake` и в среде аудита не запускался. Вердикт `proved = 5` почти
наверняка изменится. `README.md` и `PUBLIC_CLAIM_SHEET.md` п. 23 после этого
потребуют правки — они публичные, и я их не трогал.

Известное ограничение: `context_normalization` не помечается, потому что
`positive_operator` не входит в список запрещённого для этого обязательства.
Файл действительно вещественный, но PSD в нём постулируется определением. Стоит
ли считать это импортом — решение по теории, не по коду.

## 9. Что осталось

1. `rm -f .git/index.lock .git/HEAD.lock tests/_tmp_forbidden_import_probe.lean`
   — песочница не может удалять файлы, эти три остались после прогонов.
   **Сделано.**
2. `lake build` — 15 файлов никогда не компилировались, включая
   `ProjectiveActionProof.lean`, который числится одним из пяти `proved`.
   **Сделано; диагноз был неверен, см. 10.1.**
3. Прогнать `evaluate_full_qm_proof_closure.py` и обновить `proved = 5`.
   **Сделано: `proved = 2`, см. 10.4.**
4. Правка `README.md` и `PUBLIC_CLAIM_SHEET.md` п. 23 под новый вердикт.
   **Сделано, коммит `538b9b6`.**
5. Переформулировать F так, чтобы она не отрицала контекстуальность; текущая
   версия в `V7FPrimitiveIndependence.lean` заведомо ложна. **Открыто.**
6. Формализовать отношение редукции между базами. Без него «нижние примитивы»
   не является утверждением. **Открыто.**

---

## 10. Прогон на машине с Lean (2026-07-27)

Toolchain: Lean 4.29.0, Lake 5.0.0, Mathlib v4.29.0, macOS arm64.
Отчёт: `build_status_report.txt` (не коммитится).

### 10.1. Главная ошибка аудита: `lake build` ничего не собирал

Аудит вывел «15 файлов никогда не компилировались» из отсутствия `.olean`.
Вывод верен, причина — нет.

В `lakefile.lean` не было `@[default_target]`. Поэтому `lake build` печатал

```
Build completed successfully (0 jobs).
```

и не компилировал ни одного файла. Зелёный результат ничего не значил. Кроме
того, 12 файлов не были перечислены в `roots` библиотеки `Proofs` и не входили
ни в одну цель сборки:

```
V8PrimitiveEmpiricalConstraintLedger      OverlapPreservationDynamicsProof
BoundaryReversibleCompletionProbe         PairHistoryMeasureProbe
ContextFirstBellCountermodel              ProjectiveActionProof
ContextFirstReadoutUnderdeterminationProbe StringTheoryPrimitiveHintAudit
ContextualNoSignallingPRCountermodel      TwoPostulateReconstructionImportAudit
OrientedRelationalProcessCountermodel     TypedRewriteStructureUnderdeterminationProbe
```

**Все 12 компилируются без ошибок** под `lake env lean`. В том числе
`ProjectiveActionProof.lean`, поэтому карточка `projective_action` прогоном не
опровергнута — опасение из раздела 9 не подтвердилось. То же для
`OverlapPreservationDynamicsProof.lean`, на котором держится запись о bridge
wall.

После добавления `@[default_target]` и этих 12 файлов в `roots` сборка стала
осмысленной: `lake build` проходит 8375 задач.

### 10.2. Что действительно не компилировалось

Реально сломанных файлов было два, и оба по одной и той же причине, которую
статический аудит не поймал: **терм-доказательство использовалось как тип**.

- `V7BoundedCorrelations.lean:54` — `axiom facticizationStability : True`
  объявляет обитателя `True`, то есть доказательство, а не пропозицию. Запись
  `facticizationStability → True` не типизируется. Файл не компилировался
  никогда.
- `V7PositiveGeometryTwoAlternatives.lean` — `def Real := Rat` нередуцируем
  при поиске инстансов, поэтому `*`, `≥` и литерал `0` остались без
  `HMul`/`LE`/`OfNat`.

Обе ошибки исправлены минимально, без изменения того, что файлы утверждают
(а утверждают они по-прежнему ничего).

### 10.3. Чего аудит не увидел вовсе: цепочки вывода не существует

Это результат, которого в разделах 1–9 нет.

Секция 175 и заголовки файлов описывают цепочку
`B0 → product exhaustion → local tomography → bounded correlations →
Hilbert carrier → Born rule`. В Lean этой цепочки нет:

1. `V7HilbertCarrierSelection.lean` импортировал четыре модуля и **не
   использовал ни одного имени из них**. Все антецеденты объявлены в нём
   заново как `True`. То же у `V7BornRuleDerivation.lean` относительно
   `V7HilbertCarrierSelection`.
2. Импорты были взаимно несовместимы: `V7ProductContextExhaustion` и
   `V7LocalTomography` оба объявляют `IDT.QMClosure.Ctx`, поэтому импорт обоих
   — ошибка дублирующего объявления. `V7HilbertCarrierSelection` не мог
   скомпилироваться ни при каких условиях.
3. Та же ошибка «терм как тип», что в 10.2, есть в
   `V7MetricGeometryProjection`, `V7HilbertCarrierSelection` и
   `V7BornRuleDerivation`.

То есть каждое звено переобъявляет вывод предыдущего как свежий `True` и ни на
что не ссылается. Импорты удалены, а не починены: чинить их значило бы
утверждать зависимость, которой в Lean нет.

Побочно: `quadraticFromCarrier` был спрятан за `axiom ... : True` и не
попадал в счётчик пустых теорем. После перевода в `def ... : Prop := True`
счётчик вырос с 32 до 33 — то есть видимость пустоты увеличилась, а не
уменьшилась.

### 10.4. Вердикт closure-эвалуатора

Предсказание раздела 8.3 подтвердилось полностью:

```
full_qm_proof_closure=IMPORTED_ASSUMPTION_REJECTED
route_status=CONDITIONAL_FULL_QM_ROUTE
proved=2  imported_artifacts=3  conditional_artifacts=16  missing_artifacts=0
```

```
PROVED          context_normalization      [born_readout]
PROVED          projective_action          [dynamics]
IMPORT_REJECTED exclusivity_additivity     — forbidden target import: hilbert_space
IMPORT_REJECTED coarse_graining_consistency — то же
IMPORT_REJECTED operational_equivalence_probability — то же
```

`README.md` и `PUBLIC_CLAIM_SHEET.md` п. 23 приведены в соответствие
(коммит `538b9b6`). Формулировка п. 23 о том, что тело каждого из пяти
артефактов сканируется, «so that none of them silently imports Hilbert-space
machinery», заменена на прямое признание: три из пяти несут собранный вручную
комплексный носитель.

### 10.5. Коммит `b60e055` ломал сборку

Маркеры `EMPTY_PLACEHOLDER` были вставлены **выше** строк `import`. Lean это
запрещает: `invalid 'import' command, it must be used in the beginning of the
file`. Из-за этого перестали компилироваться пять файлов, четыре из которых
до `b60e055` компилировались:

```
V8QmResearchTaskLedger  V7HilbertCarrierSelection  V7BornRuleDerivation
V7MetricGeometryProjection  V7DimensionAnalysis
```

Маркеры перенесены под импорты. Ни один маркер не снят. Прямое следствие того,
что среда аудита не могла запустить компилятор.

### 10.6. Тесты

Шесть ошибок в `tests/test_evaluate_full_qm_proof_closure.py`, наблюдавшихся в
контейнере, **не воспроизвелись**: `583 passed, 2 skipped`. Они были артефактом
песочницы, как и предполагалось.

Прочие гейты: `check_proofs`, `sync_formal_proof_ledger --check`,
`theory_verifier` (`ok=true`, `issues=0`), `evaluate_full_qm_proof_attempt`,
`check_vacuous_theorems`, `ruff`, `git diff --check` — все проходят.
`evaluate_full_qm_proof_closure` возвращает 1, и это правильное поведение:
он отвергает импорт.

### 10.7. Осталось решением, а не патчем

- `proved = 5` осталось в комментариях
  `Proofs/MetaLang/V8QmResearchTaskLedger.lean` (строки ~913, 1045, 1152) и в
  `sections/174-...md`. Это исторические записи прошлых сессий; вносить в
  Lean-ledger новую запись о вердикте — работа по теории, не правка текста.
- Стоит ли удалить пустые файлы `V7*` целиком вместо того, чтобы держать их
  компилируемыми и помеченными. Сейчас выбран второй вариант: он сохраняет
  запись о том, что было предпринято.
- `context_normalization` не помечается сканером, потому что
  `positive_operator` не входит в список запрещённого для этого обязательства,
  хотя PSD в файле постулируется определением (см. конец 8.3).
