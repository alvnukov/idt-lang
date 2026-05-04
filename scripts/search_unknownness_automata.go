package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"hash/fnv"
	"math"
	"math/rand"
	"os"
	"runtime"
	"sort"
	"strings"
	"sync"
	"time"
)

type State uint8
type Rule [64]State

const (
	Empty State = iota
	Plus
	Minus
	Residue
)

var stateNames = [...]string{"_", "+", "-", "X"}

type Counts struct {
	Dead        int `json:"dead"`
	Frozen      int `json:"frozen"`
	Periodic    int `json:"periodic"`
	Moving      int `json:"moving"`
	Chaotic     int `json:"chaotic"`
	ResidueSeen int `json:"residue_seen"`
}

type XAudit struct {
	CreatedFromConflict    int `json:"x_created_from_conflict"`
	CreatedFromNonConflict int `json:"x_created_from_nonconflict"`
	Participations         int `json:"x_participations"`
	ChangedOutput          int `json:"x_changed_output"`
	ToRecord               int `json:"x_to_record"`
	BlocksRecord           int `json:"x_blocks_record"`
	RedirectsRecord        int `json:"x_redirects_record"`
}

type Result struct {
	Score  int
	Rule   Rule
	Counts Counts
}

type Config struct {
	Mode                    string
	Samples                 int
	Size                    int
	Steps                   int
	BurnIn                  int
	Seed                    int64
	Keep                    int
	Workers                 int
	Population              int
	Generations             int
	Elites                  int
	Immigrants              int
	MutationCount           int
	ActivityMin             int
	ActivityMax             int
	ResidueCritical         bool
	RequireResidueCritical  bool
	RequireDead             bool
	RequireFrozen           bool
	MaxXToRecordRatio       float64
	RequireXChangesOutput   bool
	ShowRule                bool
	PairedControls          bool
	AuditX                  bool
	EstimateCandidateCounts bool
	ProgressEvery           int
	OutputJSONL             string
}

type JSONResult struct {
	Rank             int               `json:"rank"`
	Score            int               `json:"score"`
	Counts           Counts            `json:"counts"`
	PairedControls   map[string]Counts `json:"paired_controls,omitempty"`
	XAudit           *XAudit           `json:"x_audit,omitempty"`
	Rule             string            `json:"rule"`
	RuleTable        string            `json:"rule_table,omitempty"`
	MotifSignature   string            `json:"motif_signature"`
	CriticalTriples  []string          `json:"critical_triples"`
	ResidueAffects   bool              `json:"residue_affects"`
	ActiveCount      int               `json:"active_count"`
	InertActiveCount int               `json:"inert_active_count"`
	Config           map[string]string `json:"config"`
}

func flipState(state State) State {
	switch state {
	case Plus:
		return Minus
	case Minus:
		return Plus
	default:
		return state
	}
}

func indexOf(left State, center State, right State) int {
	return int(left)*16 + int(center)*4 + int(right)
}

func tripleOf(index int) (State, State, State) {
	left := State(index / 16)
	rest := index % 16
	center := State(rest / 4)
	right := State(rest % 4)
	return left, center, right
}

func flipTriple(left State, center State, right State) (State, State, State) {
	return flipState(left), flipState(center), flipState(right)
}

func inertTriple(left State, center State, right State) (State, State, State) {
	if left == Residue {
		left = Empty
	}
	if center == Residue {
		center = Empty
	}
	if right == Residue {
		right = Empty
	}
	return left, center, right
}

func hasConflict(left State, center State, right State) bool {
	hasPlus := left == Plus || center == Plus || right == Plus
	hasMinus := left == Minus || center == Minus || right == Minus
	return hasPlus && hasMinus
}

func allowedOutputs(left State, center State, right State, eraseConflict bool) []State {
	if hasConflict(left, center, right) {
		if eraseConflict {
			return []State{Empty}
		}
		return []State{Residue}
	}
	hasPlus := left == Plus || center == Plus || right == Plus
	hasMinus := left == Minus || center == Minus || right == Minus
	if hasPlus && !hasMinus {
		return []State{Empty, Plus, Residue}
	}
	if hasMinus && !hasPlus {
		return []State{Empty, Minus, Residue}
	}
	return []State{Empty, Residue}
}

func setEquivariant(table *[64]int8, left State, center State, right State, output State) {
	index := indexOf(left, center, right)
	fl, fc, fr := flipTriple(left, center, right)
	flippedIndex := indexOf(fl, fc, fr)
	existing := table[index]
	if existing >= 0 && State(existing) != output {
		panic("conflicting table output")
	}
	flippedOutput := flipState(output)
	flippedExisting := table[flippedIndex]
	if flippedExisting >= 0 && State(flippedExisting) != flippedOutput {
		panic("conflicting flipped table output")
	}
	table[index] = int8(output)
	table[flippedIndex] = int8(flippedOutput)
}

func setEquivariantRule(rule *Rule, left State, center State, right State, output State) {
	index := indexOf(left, center, right)
	fl, fc, fr := flipTriple(left, center, right)
	rule[index] = output
	rule[indexOf(fl, fc, fr)] = flipState(output)
}

func seededTable(control string) [64]int8 {
	var table [64]int8
	for i := range table {
		table[i] = -1
	}
	inertX := control == "inert-x"
	eraseConflict := control == "erase-conflict"

	setEquivariant(&table, Empty, Empty, Empty, Empty)
	if !inertX {
		setEquivariant(&table, Residue, Residue, Residue, Residue)
	}
	setEquivariant(&table, Plus, Plus, Plus, Plus)
	setEquivariant(&table, Empty, Plus, Empty, Empty)
	setEquivariant(&table, Plus, Empty, Plus, Plus)
	if !inertX {
		setEquivariant(&table, Empty, Residue, Empty, Empty)
		setEquivariant(&table, Residue, Empty, Residue, Residue)
	}
	for left := State(0); left < 4; left++ {
		for center := State(0); center < 4; center++ {
			for right := State(0); right < 4; right++ {
				if hasConflict(left, center, right) {
					output := Residue
					if eraseConflict {
						output = Empty
					}
					setEquivariant(&table, left, center, right, output)
				}
			}
		}
	}
	return table
}

func randomRule(rng *rand.Rand, control string) Rule {
	table := seededTable(control)
	inertX := control == "inert-x"
	eraseConflict := control == "erase-conflict"

	for pass := 0; pass < 2; pass++ {
		for index, value := range table {
			if value >= 0 {
				continue
			}
			left, center, right := tripleOf(index)
			if inertX && (left == Residue || center == Residue || right == Residue) {
				if pass == 0 {
					continue
				}
				nl, nc, nr := inertTriple(left, center, right)
				normalized := table[indexOf(nl, nc, nr)]
				if normalized < 0 {
					panic("inert normalized triple was not initialized")
				}
				setEquivariant(&table, left, center, right, State(normalized))
				continue
			}
			fl, fc, fr := flipTriple(left, center, right)
			flippedIndex := indexOf(fl, fc, fr)
			if flippedIndex < index {
				continue
			}
			var output State
			if fl == left && fc == center && fr == right {
				if rng.Intn(2) == 0 {
					output = Empty
				} else {
					output = Residue
				}
			} else {
				choices := allowedOutputs(left, center, right, eraseConflict)
				output = choices[rng.Intn(len(choices))]
			}
			setEquivariant(&table, left, center, right, output)
		}
	}

	var rule Rule
	for index, value := range table {
		if value < 0 {
			rule[index] = Empty
		} else {
			rule[index] = State(value)
		}
	}
	return rule
}

func mutableOrbitRepresentatives(control string) []int {
	table := seededTable(control)
	reps := make([]int, 0)
	for index, value := range table {
		left, center, right := tripleOf(index)
		if control == "inert-x" && (left == Residue || center == Residue || right == Residue) {
			continue
		}
		fl, fc, fr := flipTriple(left, center, right)
		flippedIndex := indexOf(fl, fc, fr)
		if flippedIndex < index || value >= 0 {
			continue
		}
		reps = append(reps, index)
	}
	return reps
}

func mutatedRule(base Rule, rng *rand.Rand, representatives []int, control string, mutationCount int) Rule {
	rule := base
	if mutationCount <= 0 {
		mutationCount = 1
	}
	eraseConflict := control == "erase-conflict"
	for i := 0; i < mutationCount; i++ {
		rep := representatives[rng.Intn(len(representatives))]
		left, center, right := tripleOf(rep)
		choices := allowedOutputs(left, center, right, eraseConflict)
		current := rule[rep]
		if len(choices) <= 1 {
			continue
		}
		next := current
		for next == current {
			next = choices[rng.Intn(len(choices))]
		}
		setEquivariantRule(&rule, left, center, right, next)
	}
	return rule
}

func step(rule Rule, cells []State, next []State) {
	size := len(cells)
	for i, center := range cells {
		left := cells[(i-1+size)%size]
		right := cells[(i+1)%size]
		next[i] = rule[indexOf(left, center, right)]
	}
}

func allEmpty(cells []State) bool {
	for _, state := range cells {
		if state != Empty {
			return false
		}
	}
	return true
}

func containsResidue(cells []State) bool {
	for _, state := range cells {
		if state == Residue {
			return true
		}
	}
	return false
}

func key(cells []State) string {
	bytes := make([]byte, len(cells))
	for i, state := range cells {
		bytes[i] = byte('0' + state)
	}
	return string(bytes)
}

func rotateKey(cells []State, offset int) string {
	size := len(cells)
	bytes := make([]byte, size)
	for i := 0; i < size; i++ {
		bytes[i] = byte('0' + cells[(i+offset)%size])
	}
	return string(bytes)
}

func canonicalRotationKey(cells []State) string {
	best := rotateKey(cells, 0)
	for offset := 1; offset < len(cells); offset++ {
		candidate := rotateKey(cells, offset)
		if candidate < best {
			best = candidate
		}
	}
	return best
}

func simulate(rule Rule, seed []State, steps int, burnIn int) (string, bool) {
	cells := append([]State(nil), seed...)
	next := make([]State, len(cells))
	seenRaw := make(map[string]int)
	seenCanonical := make(map[string]string)
	residueSeen := containsResidue(cells)

	for t := 0; t <= steps; t++ {
		if containsResidue(cells) {
			residueSeen = true
		}
		if t >= burnIn {
			if allEmpty(cells) {
				return "dead", residueSeen
			}
			raw := key(cells)
			if previous, ok := seenRaw[raw]; ok {
				if t-previous == 1 {
					return "frozen", residueSeen
				}
				return "periodic", residueSeen
			}
			seenRaw[raw] = t
			canonical := canonicalRotationKey(cells)
			if previous, ok := seenCanonical[canonical]; ok && previous != raw {
				return "moving", residueSeen
			}
			seenCanonical[canonical] = raw
		}
		step(rule, cells, next)
		cells, next = next, cells
	}
	return "chaotic", residueSeen
}

func buildSeeds(size int, rng *rand.Rand, randomSeedCount int) [][]State {
	seeds := make([][]State, 0, randomSeedCount+6)
	empty := make([]State, size)
	seeds = append(seeds, empty)
	allPlus := make([]State, size)
	for i := range allPlus {
		allPlus[i] = Plus
	}
	seeds = append(seeds, allPlus)
	single := make([]State, size)
	single[size/2] = Plus
	seeds = append(seeds, single)
	gap := make([]State, size)
	gap[size/2-1] = Plus
	gap[size/2+1] = Plus
	seeds = append(seeds, gap)
	conflict := make([]State, size)
	conflict[size/2-1] = Plus
	conflict[size/2+1] = Minus
	seeds = append(seeds, conflict)
	residue := make([]State, size)
	residue[size/2] = Residue
	seeds = append(seeds, residue)
	for i := 0; i < randomSeedCount; i++ {
		cells := make([]State, size)
		for j := range cells {
			roll := rng.Float64()
			switch {
			case roll < 0.70:
				cells[j] = Empty
			case roll < 0.82:
				cells[j] = Plus
			case roll < 0.94:
				cells[j] = Minus
			default:
				cells[j] = Residue
			}
		}
		seeds = append(seeds, cells)
	}
	return seeds
}

func activeCount(counts Counts) int {
	return counts.Periodic + counts.Moving
}

func residueAffectsRule(rule Rule) bool {
	for index, output := range rule {
		left, center, right := tripleOf(index)
		if left != Residue && center != Residue && right != Residue {
			continue
		}
		nl, nc, nr := inertTriple(left, center, right)
		if output != rule[indexOf(nl, nc, nr)] {
			return true
		}
	}
	return false
}

func inertizedRule(rule Rule) Rule {
	next := rule
	for index := range next {
		left, center, right := tripleOf(index)
		if left == Residue || center == Residue || right == Residue {
			nl, nc, nr := inertTriple(left, center, right)
			next[index] = rule[indexOf(nl, nc, nr)]
		}
	}
	return next
}

func conflictErasedRule(rule Rule) Rule {
	next := rule
	for index := range next {
		left, center, right := tripleOf(index)
		if hasConflict(left, center, right) {
			next[index] = Empty
		}
	}
	return next
}

func auditX(rule Rule, seeds [][]State, steps int) XAudit {
	var audit XAudit
	for _, seed := range seeds {
		cells := append([]State(nil), seed...)
		next := make([]State, len(cells))
		size := len(cells)
		for t := 0; t < steps; t++ {
			for i, center := range cells {
				left := cells[(i-1+size)%size]
				right := cells[(i+1)%size]
				output := rule[indexOf(left, center, right)]
				nl, nc, nr := inertTriple(left, center, right)
				inertOutput := rule[indexOf(nl, nc, nr)]
				hasResidue := left == Residue || center == Residue || right == Residue
				if output == Residue && !hasResidue {
					if hasConflict(left, center, right) {
						audit.CreatedFromConflict++
					} else {
						audit.CreatedFromNonConflict++
					}
				}
				if hasResidue {
					audit.Participations++
					if output != inertOutput {
						audit.ChangedOutput++
					}
					if output == Plus || output == Minus {
						audit.ToRecord++
					}
					if (inertOutput == Plus || inertOutput == Minus) && output != Plus && output != Minus {
						audit.BlocksRecord++
					}
					if (output == Plus || output == Minus) && output != inertOutput {
						audit.RedirectsRecord++
					}
				}
			}
			step(rule, cells, next)
			cells, next = next, cells
		}
	}
	return audit
}

func scoreRule(rule Rule, seeds [][]State, cfg Config, residueCritical bool) (int, Counts, bool) {
	var counts Counts
	for _, seed := range seeds {
		label, residueSeen := simulate(rule, seed, cfg.Steps, cfg.BurnIn)
		switch label {
		case "dead":
			counts.Dead++
		case "frozen":
			counts.Frozen++
		case "periodic":
			counts.Periodic++
		case "moving":
			counts.Moving++
		default:
			counts.Chaotic++
		}
		if residueSeen {
			counts.ResidueSeen++
		}
	}
	active := activeCount(counts)
	boring := counts.Dead + counts.Frozen
	if cfg.ActivityMin >= 0 && active < cfg.ActivityMin {
		return 0, counts, false
	}
	if cfg.ActivityMax >= 0 && active > cfg.ActivityMax {
		return 0, counts, false
	}
	if cfg.RequireDead && counts.Dead == 0 {
		return 0, counts, false
	}
	if cfg.RequireFrozen && counts.Frozen == 0 {
		return 0, counts, false
	}

	score := 0
	if residueAffectsRule(rule) {
		score += 4
	} else {
		score -= 8
	}
	if counts.Dead > 0 {
		score += 5
	} else {
		score -= 3
	}
	if counts.Frozen > 0 {
		score += 5
	} else {
		score -= 3
	}
	if active > 0 {
		score += 8
	} else {
		score -= 8
	}
	if counts.Moving > 0 {
		score += 5
	}
	if counts.Chaotic > 0 {
		score += 3
	}
	if active == len(seeds) {
		score -= 5
	}
	if boring == len(seeds) {
		score -= 5
	}
	score += counts.ResidueSeen

	if residueCritical {
		_, inertCounts, _ := scoreRule(inertizedRule(rule), seeds, cfg, false)
		activeDelta := active - activeCount(inertCounts)
		if activeDelta > 0 {
			score += activeDelta * 4
		}
		if active > 0 && activeDelta <= 0 {
			score -= 10
		}
		if cfg.RequireResidueCritical && activeDelta <= 0 {
			return 0, counts, false
		}
	}

	if cfg.RequireXChangesOutput || cfg.MaxXToRecordRatio >= 0 {
		audit := auditX(rule, seeds, cfg.Steps)
		if cfg.RequireXChangesOutput && audit.ChangedOutput == 0 {
			return 0, counts, false
		}
		if cfg.MaxXToRecordRatio >= 0 && audit.Participations > 0 {
			ratio := float64(audit.ToRecord) / float64(audit.Participations)
			if ratio > cfg.MaxXToRecordRatio {
				return 0, counts, false
			}
		}
	}
	return score, counts, true
}

func insertBest(best []Result, candidate Result, keep int) []Result {
	best = append(best, candidate)
	sort.Slice(best, func(i int, j int) bool {
		return best[i].Score > best[j].Score
	})
	if len(best) > keep {
		best = best[:keep]
	}
	return best
}

func workerSearch(workerID int, samples int, cfg Config, output chan<- []Result) {
	rng := rand.New(rand.NewSource(cfg.Seed + int64(workerID)*1_000_003))
	seeds := buildSeeds(cfg.Size, rand.New(rand.NewSource(cfg.Seed)), 10)
	best := make([]Result, 0, cfg.Keep)
	start := time.Now()
	for i := 0; i < samples; i++ {
		rule := randomRule(rng, "u0")
		score, counts, ok := scoreRule(rule, seeds, cfg, cfg.ResidueCritical)
		if cfg.ProgressEvery > 0 && (i+1)%cfg.ProgressEvery == 0 {
			bestScore := 0
			if len(best) > 0 {
				bestScore = best[0].Score
			}
			fmt.Fprintf(
				os.Stderr,
				"progress worker=%d processed=%d/%d elapsed=%s local_best=%d\n",
				workerID,
				i+1,
				samples,
				time.Since(start).Round(time.Second),
				bestScore,
			)
		}
		if !ok {
			continue
		}
		if len(best) < cfg.Keep || score > best[len(best)-1].Score {
			best = insertBest(best, Result{Score: score, Rule: rule, Counts: counts}, cfg.Keep)
		}
	}
	output <- best
}

func search(cfg Config) []Result {
	workers := cfg.Workers
	if workers <= 0 {
		workers = runtime.NumCPU()
	}
	if workers > cfg.Samples {
		workers = cfg.Samples
	}
	output := make(chan []Result, workers)
	var wg sync.WaitGroup
	base := cfg.Samples / workers
	remainder := cfg.Samples % workers
	for worker := 0; worker < workers; worker++ {
		samples := base
		if worker < remainder {
			samples++
		}
		wg.Add(1)
		go func(workerID int, workerSamples int) {
			defer wg.Done()
			workerSearch(workerID, workerSamples, cfg, output)
		}(worker, samples)
	}
	wg.Wait()
	close(output)
	best := make([]Result, 0, cfg.Keep)
	for localBest := range output {
		for _, candidate := range localBest {
			best = insertBest(best, candidate, cfg.Keep)
		}
	}
	return best
}

func evaluatePopulation(rules []Rule, seeds [][]State, cfg Config) []Result {
	workers := cfg.Workers
	if workers <= 0 {
		workers = runtime.NumCPU()
	}
	if workers > len(rules) {
		workers = len(rules)
	}
	if workers <= 0 {
		return nil
	}

	jobs := make(chan Rule)
	results := make(chan Result, len(rules))
	var wg sync.WaitGroup
	for worker := 0; worker < workers; worker++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for rule := range jobs {
				score, counts, ok := scoreRule(rule, seeds, cfg, cfg.ResidueCritical)
				if ok {
					results <- Result{Score: score, Rule: rule, Counts: counts}
				}
			}
		}()
	}
	for _, rule := range rules {
		jobs <- rule
	}
	close(jobs)
	wg.Wait()
	close(results)

	evaluated := make([]Result, 0, len(rules))
	for result := range results {
		evaluated = append(evaluated, result)
	}
	sort.Slice(evaluated, func(i int, j int) bool {
		return evaluated[i].Score > evaluated[j].Score
	})
	return evaluated
}

func evolveSearch(cfg Config) []Result {
	populationSize := cfg.Population
	if populationSize <= 0 {
		populationSize = 2_000
	}
	generations := cfg.Generations
	if generations <= 0 {
		generations = 50
	}
	elites := cfg.Elites
	if elites <= 0 {
		elites = populationSize / 20
	}
	if elites < 1 {
		elites = 1
	}
	if elites > populationSize {
		elites = populationSize
	}
	immigrants := cfg.Immigrants
	if immigrants < 0 {
		immigrants = 0
	}
	if immigrants > populationSize-elites {
		immigrants = populationSize - elites
	}

	rng := rand.New(rand.NewSource(cfg.Seed))
	seeds := buildSeeds(cfg.Size, rand.New(rand.NewSource(cfg.Seed)), 10)
	representatives := mutableOrbitRepresentatives("u0")
	population := make([]Rule, populationSize)
	for i := range population {
		population[i] = randomRule(rng, "u0")
	}

	globalBest := make([]Result, 0, cfg.Keep)
	start := time.Now()
	for generation := 1; generation <= generations; generation++ {
		evaluated := evaluatePopulation(population, seeds, cfg)
		for _, result := range evaluated {
			globalBest = insertBest(globalBest, result, cfg.Keep)
		}

		if cfg.ProgressEvery > 0 && generation%cfg.ProgressEvery == 0 {
			bestScore := 0
			globalBestScore := 0
			survivors := len(evaluated)
			if len(evaluated) > 0 {
				bestScore = evaluated[0].Score
			}
			if len(globalBest) > 0 {
				globalBestScore = globalBest[0].Score
			}
			fmt.Fprintf(
				os.Stderr,
				"evolve generation=%d/%d elapsed=%s survivors=%d best=%d global_best=%d\n",
				generation,
				generations,
				time.Since(start).Round(time.Second),
				survivors,
				bestScore,
				globalBestScore,
			)
		}

		parents := evaluated
		if len(parents) == 0 {
			parents = make([]Result, elites)
			for i := range parents {
				parents[i] = Result{Rule: randomRule(rng, "u0")}
			}
		}
		if len(parents) > elites {
			parents = parents[:elites]
		}

		next := make([]Rule, 0, populationSize)
		for _, parent := range parents {
			next = append(next, parent.Rule)
		}
		randomSlots := immigrants
		for len(next) < populationSize-randomSlots {
			parent := parents[rng.Intn(len(parents))].Rule
			next = append(next, mutatedRule(parent, rng, representatives, "u0", cfg.MutationCount))
		}
		for len(next) < populationSize {
			next = append(next, randomRule(rng, "u0"))
		}
		population = next
	}
	return globalBest
}

func renderRule(rule Rule) string {
	parts := make([]string, 0, len(rule))
	for index, output := range rule {
		left, center, right := tripleOf(index)
		parts = append(parts, fmt.Sprintf("%s%s%s->%s", stateNames[left], stateNames[center], stateNames[right], stateNames[output]))
	}
	return strings.Join(parts, " ")
}

func compactRule(rule Rule) string {
	bytes := make([]byte, len(rule))
	for index, output := range rule {
		bytes[index] = byte('0' + output)
	}
	return string(bytes)
}

func transitionName(index int, output State) string {
	left, center, right := tripleOf(index)
	return fmt.Sprintf("%s%s%s->%s", stateNames[left], stateNames[center], stateNames[right], stateNames[output])
}

func criticalTriples(rule Rule) []string {
	triples := make([]string, 0)
	for index, output := range rule {
		left, center, right := tripleOf(index)
		hasResidue := left == Residue || center == Residue || right == Residue
		if hasResidue {
			nl, nc, nr := inertTriple(left, center, right)
			if output != rule[indexOf(nl, nc, nr)] {
				triples = append(triples, transitionName(index, output))
			}
			continue
		}
		if output == Residue && !hasConflict(left, center, right) {
			triples = append(triples, transitionName(index, output))
		}
	}
	return triples
}

func motifSignature(rule Rule) string {
	xInputs := 0
	xChanged := 0
	xToRecord := 0
	xCreatesNonConflict := 0
	for index, output := range rule {
		left, center, right := tripleOf(index)
		hasResidue := left == Residue || center == Residue || right == Residue
		if hasResidue {
			xInputs++
			nl, nc, nr := inertTriple(left, center, right)
			if output != rule[indexOf(nl, nc, nr)] {
				xChanged++
			}
			if output == Plus || output == Minus {
				xToRecord++
			}
		} else if output == Residue && !hasConflict(left, center, right) {
			xCreatesNonConflict++
		}
	}
	critical := strings.Join(criticalTriples(rule), "|")
	hasher := fnv.New64a()
	_, _ = hasher.Write([]byte(critical))
	return fmt.Sprintf(
		"x_inputs=%d;x_changed=%d;x_to_record=%d;x_create_nonconflict=%d;critical_hash=%016x",
		xInputs,
		xChanged,
		xToRecord,
		xCreatesNonConflict,
		hasher.Sum64(),
	)
}

func printResult(rank int, result Result, cfg Config) {
	fmt.Printf(
		"rank=%d score=%d counts={dead:%d frozen:%d periodic:%d moving:%d chaotic:%d residue_seen:%d} residue_affects=%t\n",
		rank,
		result.Score,
		result.Counts.Dead,
		result.Counts.Frozen,
		result.Counts.Periodic,
		result.Counts.Moving,
		result.Counts.Chaotic,
		result.Counts.ResidueSeen,
		residueAffectsRule(result.Rule),
	)
	seeds := buildSeeds(cfg.Size, rand.New(rand.NewSource(cfg.Seed)), 10)
	if cfg.PairedControls {
		pairedCfg := cfg
		pairedCfg.ActivityMin = -1
		pairedCfg.ActivityMax = -1
		pairedCfg.RequireDead = false
		pairedCfg.RequireFrozen = false
		pairedCfg.RequireResidueCritical = false
		pairedCfg.RequireXChangesOutput = false
		pairedCfg.MaxXToRecordRatio = -1
		for _, item := range []struct {
			label string
			rule  Rule
		}{
			{"paired-inert-x", inertizedRule(result.Rule)},
			{"paired-erase-conflict", conflictErasedRule(result.Rule)},
		} {
			score, counts, _ := scoreRule(item.rule, seeds, pairedCfg, false)
			fmt.Printf(
				"control=%s source_rank=%d score=%d counts={dead:%d frozen:%d periodic:%d moving:%d chaotic:%d residue_seen:%d} residue_affects=%t\n",
				item.label,
				rank,
				score,
				counts.Dead,
				counts.Frozen,
				counts.Periodic,
				counts.Moving,
				counts.Chaotic,
				counts.ResidueSeen,
				residueAffectsRule(item.rule),
			)
		}
	}
	if cfg.AuditX {
		audit := auditX(result.Rule, seeds, cfg.Steps)
		fmt.Printf(
			"x_audit={x_created_from_conflict:%d x_created_from_nonconflict:%d x_participations:%d x_changed_output:%d x_to_record:%d x_blocks_record:%d x_redirects_record:%d}\n",
			audit.CreatedFromConflict,
			audit.CreatedFromNonConflict,
			audit.Participations,
			audit.ChangedOutput,
			audit.ToRecord,
			audit.BlocksRecord,
			audit.RedirectsRecord,
		)
	}
	if cfg.ShowRule {
		fmt.Println(renderRule(result.Rule))
	}
}

func pairedCounts(rule Rule, seeds [][]State, cfg Config) map[string]Counts {
	pairedCfg := cfg
	pairedCfg.ActivityMin = -1
	pairedCfg.ActivityMax = -1
	pairedCfg.RequireDead = false
	pairedCfg.RequireFrozen = false
	pairedCfg.RequireResidueCritical = false
	pairedCfg.RequireXChangesOutput = false
	pairedCfg.MaxXToRecordRatio = -1
	output := make(map[string]Counts)
	_, inertCounts, _ := scoreRule(inertizedRule(rule), seeds, pairedCfg, false)
	_, erasedCounts, _ := scoreRule(conflictErasedRule(rule), seeds, pairedCfg, false)
	output["paired-inert-x"] = inertCounts
	output["paired-erase-conflict"] = erasedCounts
	return output
}

func configSummary(cfg Config) map[string]string {
	return map[string]string{
		"mode":                        cfg.Mode,
		"samples":                     fmt.Sprintf("%d", cfg.Samples),
		"population":                  fmt.Sprintf("%d", cfg.Population),
		"generations":                 fmt.Sprintf("%d", cfg.Generations),
		"elites":                      fmt.Sprintf("%d", cfg.Elites),
		"immigrants":                  fmt.Sprintf("%d", cfg.Immigrants),
		"mutation_count":              fmt.Sprintf("%d", cfg.MutationCount),
		"size":                        fmt.Sprintf("%d", cfg.Size),
		"steps":                       fmt.Sprintf("%d", cfg.Steps),
		"burn_in":                     fmt.Sprintf("%d", cfg.BurnIn),
		"seed":                        fmt.Sprintf("%d", cfg.Seed),
		"workers":                     fmt.Sprintf("%d", cfg.Workers),
		"activity_min":                fmt.Sprintf("%d", cfg.ActivityMin),
		"activity_max":                fmt.Sprintf("%d", cfg.ActivityMax),
		"residue_critical":            fmt.Sprintf("%t", cfg.ResidueCritical),
		"require_residue_critical":    fmt.Sprintf("%t", cfg.RequireResidueCritical),
		"require_dead":                fmt.Sprintf("%t", cfg.RequireDead),
		"require_frozen":              fmt.Sprintf("%t", cfg.RequireFrozen),
		"max_x_to_record_ratio":       fmt.Sprintf("%.6g", cfg.MaxXToRecordRatio),
		"require_x_changes_output":    fmt.Sprintf("%t", cfg.RequireXChangesOutput),
		"constrained_candidate_space": "688747536",
	}
}

func resultRecord(rank int, result Result, cfg Config, seeds [][]State) JSONResult {
	var audit *XAudit
	if cfg.AuditX {
		value := auditX(result.Rule, seeds, cfg.Steps)
		audit = &value
	}
	paired := pairedCounts(result.Rule, seeds, cfg)
	return JSONResult{
		Rank:             rank,
		Score:            result.Score,
		Counts:           result.Counts,
		PairedControls:   paired,
		XAudit:           audit,
		Rule:             compactRule(result.Rule),
		RuleTable:        renderRule(result.Rule),
		MotifSignature:   motifSignature(result.Rule),
		CriticalTriples:  criticalTriples(result.Rule),
		ResidueAffects:   residueAffectsRule(result.Rule),
		ActiveCount:      activeCount(result.Counts),
		InertActiveCount: activeCount(paired["paired-inert-x"]),
		Config:           configSummary(cfg),
	}
}

func writeJSONL(path string, best []Result, cfg Config) error {
	file, err := os.Create(path)
	if err != nil {
		return err
	}
	defer file.Close()
	encoder := json.NewEncoder(file)
	seeds := buildSeeds(cfg.Size, rand.New(rand.NewSource(cfg.Seed)), 10)
	for rank, result := range best {
		if err := encoder.Encode(resultRecord(rank+1, result, cfg, seeds)); err != nil {
			return err
		}
	}
	return nil
}

func printClusterSummary(best []Result) {
	clusters := make(map[string]int)
	for _, result := range best {
		clusters[motifSignature(result.Rule)]++
	}
	type cluster struct {
		signature string
		count     int
	}
	items := make([]cluster, 0, len(clusters))
	for signature, count := range clusters {
		items = append(items, cluster{signature: signature, count: count})
	}
	sort.Slice(items, func(i int, j int) bool {
		if items[i].count == items[j].count {
			return items[i].signature < items[j].signature
		}
		return items[i].count > items[j].count
	})
	for _, item := range items {
		fmt.Printf("cluster count=%d motif=%s\n", item.count, item.signature)
	}
}

func estimateCandidateCounts() {
	raw := math.Pow(4, 64)
	fmt.Printf("raw_radius1_4state_rules=%.3e\n", raw)
	for _, control := range []string{"u0", "inert-x", "erase-conflict"} {
		table := seededTable(control)
		choicesProduct := uint64(1)
		fixedOrbits := 0
		choiceOrbits := 0
		skippedInert := 0
		choiceHist := map[int]int{}
		for index, value := range table {
			left, center, right := tripleOf(index)
			fl, fc, fr := flipTriple(left, center, right)
			flippedIndex := indexOf(fl, fc, fr)
			if flippedIndex < index {
				continue
			}
			if value >= 0 {
				fixedOrbits++
				continue
			}
			if control == "inert-x" && (left == Residue || center == Residue || right == Residue) {
				skippedInert++
				continue
			}
			choiceCount := len(allowedOutputs(left, center, right, control == "erase-conflict"))
			if fl == left && fc == center && fr == right {
				choiceCount = 2
			}
			choiceOrbits++
			choiceHist[choiceCount]++
			choicesProduct *= uint64(choiceCount)
		}
		fmt.Printf(
			"mode=%s fixed_orbits=%d choice_orbits=%d skipped_inert_orbits=%d choices_hist=%v candidate_rules=%d scientific=%.3e\n",
			control,
			fixedOrbits,
			choiceOrbits,
			skippedInert,
			choiceHist,
			choicesProduct,
			float64(choicesProduct),
		)
	}
}

func main() {
	cfg := Config{}
	flag.StringVar(&cfg.Mode, "mode", "random", "search mode: random or evolve")
	flag.IntVar(&cfg.Samples, "samples", 100_000, "number of random U0 rules to sample")
	flag.IntVar(&cfg.Size, "size", 40, "ring size")
	flag.IntVar(&cfg.Steps, "steps", 120, "simulation steps")
	flag.IntVar(&cfg.BurnIn, "burn-in", 16, "burn-in steps before classification")
	flag.Int64Var(&cfg.Seed, "seed", 174, "base RNG seed")
	flag.IntVar(&cfg.Keep, "keep", 5, "number of best rules to keep")
	flag.IntVar(&cfg.Workers, "workers", runtime.NumCPU(), "parallel workers")
	flag.IntVar(&cfg.Population, "population", 2_000, "evolution population size")
	flag.IntVar(&cfg.Generations, "generations", 50, "evolution generation count")
	flag.IntVar(&cfg.Elites, "elites", 100, "evolution elite parent count")
	flag.IntVar(&cfg.Immigrants, "immigrants", 200, "random rules injected per evolution generation")
	flag.IntVar(&cfg.MutationCount, "mutation-count", 2, "mutable rule orbits changed per offspring")
	flag.IntVar(&cfg.ActivityMin, "activity-min", 1, "minimum moving+periodic seed count; -1 disables")
	flag.IntVar(&cfg.ActivityMax, "activity-max", 14, "maximum moving+periodic seed count; -1 disables")
	flag.BoolVar(&cfg.ResidueCritical, "residue-critical", true, "score paired inert-X degradation")
	flag.BoolVar(&cfg.RequireResidueCritical, "require-residue-critical", true, "discard rules whose active count does not drop under inert-X")
	flag.BoolVar(&cfg.RequireDead, "require-dead", true, "require at least one dead seed")
	flag.BoolVar(&cfg.RequireFrozen, "require-frozen", true, "require at least one frozen seed")
	flag.Float64Var(&cfg.MaxXToRecordRatio, "max-x-to-record-ratio", 0.20, "max X-to-record participations ratio; -1 disables")
	flag.BoolVar(&cfg.RequireXChangesOutput, "require-x-changes-output", true, "require X to alter at least one transition in simulation audit")
	flag.BoolVar(&cfg.ShowRule, "show-rule", false, "print full winning rule tables")
	flag.BoolVar(&cfg.PairedControls, "paired-controls", true, "print paired inert-X and erased-conflict controls")
	flag.BoolVar(&cfg.AuditX, "audit-x", true, "print X causality audit")
	flag.BoolVar(&cfg.EstimateCandidateCounts, "estimate-candidates", false, "print constrained candidate-space counts and exit")
	flag.IntVar(&cfg.ProgressEvery, "progress-every", 0, "print per-worker progress every N samples; 0 disables")
	flag.StringVar(&cfg.OutputJSONL, "output-jsonl", "", "write top results as JSONL to this path")
	flag.Parse()

	if cfg.EstimateCandidateCounts {
		estimateCandidateCounts()
		return
	}

	var best []Result
	switch cfg.Mode {
	case "random":
		best = search(cfg)
	case "evolve":
		best = evolveSearch(cfg)
	default:
		fmt.Fprintf(os.Stderr, "unknown mode %q; expected random or evolve\n", cfg.Mode)
		os.Exit(2)
	}
	if len(best) == 0 {
		fmt.Println("no candidates survived filters")
		return
	}
	for rank, result := range best {
		printResult(rank+1, result, cfg)
	}
	printClusterSummary(best)
	if cfg.OutputJSONL != "" {
		if err := writeJSONL(cfg.OutputJSONL, best, cfg); err != nil {
			fmt.Fprintf(os.Stderr, "failed to write JSONL output: %v\n", err)
			os.Exit(1)
		}
		fmt.Fprintf(os.Stderr, "wrote_jsonl=%s\n", cfg.OutputJSONL)
	}
}
