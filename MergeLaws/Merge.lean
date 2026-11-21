/-!
# weave's entity merge, the decision for one entity

A file is a map from entity name to its body (`none` means the entity is absent).
For every name, weave compares base, ours and theirs and decides exactly as
`ResolutionStrategy` in `weave-core/src/merge.rs` does:

* both sides agree                → take it        (Unchanged, ContentEqual, both deleted)
* ours left it as base            → take theirs    (TheirsOnly, AddedTheirs, Deleted)
* theirs left it as base          → take ours      (OursOnly, AddedOurs, Deleted)
* otherwise                       → conflict       (BothModified, ModifyDelete, BothAdded)

The inner ladder (diff3, statement and footprint merges) that may still resolve a
conflict is not modelled here; these theorems are about the decision skeleton.
-/

namespace Weave

variable {Body : Type} [DecidableEq Body]

/-- The outcome for one entity. A conflict keeps both sides, never picks one. -/
inductive Outcome (Body : Type) where
  | clean    : Option Body → Outcome Body
  | conflict : (ours theirs : Option Body) → Outcome Body
  deriving DecidableEq

/-- Swap the sides of an outcome. -/
def Outcome.swap : Outcome Body → Outcome Body
  | .clean v        => .clean v
  | .conflict o t   => .conflict t o

def Outcome.isConflict : Outcome Body → Bool
  | .clean _      => false
  | .conflict _ _ => true

/-- weave's decision for one entity. -/
def decide (base ours theirs : Option Body) : Outcome Body :=
  if ours = theirs then .clean ours
  else if ours = base then .clean theirs
  else if theirs = base then .clean ours
  else .conflict ours theirs

/-- Side-swap symmetry: merging theirs into ours is the mirror of merging ours into theirs. -/
theorem decide_swap (b o t : Option Body) :
    decide b o t = (decide b t o).swap := by
  unfold decide
  by_cases h1 : o = t <;> by_cases h2 : o = b <;> by_cases h3 : t = b <;>
    have h1' : (t = o) ↔ (o = t) := ⟨Eq.symm, Eq.symm⟩ <;>
    simp only [h1', h1, h2, h3, ite_true, ite_false, Outcome.swap] <;>
    first | rfl | (subst_vars; simp_all) | simp_all [Outcome.swap, eq_comm]

/-- Idempotence: merging a change with itself is that change. -/
theorem decide_self (b o : Option Body) : decide b o o = .clean o := by
  simp [decide]

/-- A side that did nothing yields to the side that did something. -/
theorem decide_ours_untouched (b t : Option Body) : decide b b t = .clean t := by
  unfold decide
  by_cases h : b = t <;> simp [h]

theorem decide_theirs_untouched (b o : Option Body) : decide b o b = .clean o := by
  unfold decide
  by_cases h : o = b <;> simp [h]

/-- No fabrication: a clean result is always one of the two sides, never something new. -/
theorem decide_no_fabrication (b o t v : Option Body) (h : decide b o t = .clean v) :
    v = o ∨ v = t := by
  unfold decide at h
  split at h
  · cases h; exact Or.inl rfl
  · split at h
    · cases h; exact Or.inr rfl
    · split at h
      · cases h; exact Or.inl rfl
      · cases h

/-- No lost agreement: anything both sides agree on survives the merge. -/
theorem decide_unanimous (b v : Option Body) : decide b v v = .clean v := decide_self b v

/-- A conflict happens exactly when both sides changed the entity, differently. -/
theorem decide_conflict_iff (b o t : Option Body) :
    (decide b o t).isConflict = true ↔ (o ≠ b ∧ t ≠ b ∧ o ≠ t) := by
  unfold decide
  by_cases h1 : o = t <;> by_cases h2 : o = b <;> by_cases h3 : t = b <;>
    simp only [h1, h2, h3, ite_true, ite_false, Outcome.isConflict] <;>
    first | (subst_vars; simp_all) | simp_all [Outcome.isConflict]

/-! ## Whole files -/

/-- A file: entity name ↦ body. -/
abbrev File (Name Body : Type) := Name → Option Body

variable {Name : Type}

/-- Merge two files entity by entity. -/
def mergeFile (base ours theirs : File Name Body) : Name → Outcome Body :=
  fun n => decide (base n) (ours n) (theirs n)

/-- The entities a side changed. -/
def changed (base side : File Name Body) (n : Name) : Prop := side n ≠ base n

/-- **Two agents editing different functions never conflict.**
If no entity was changed by both sides, every entity merges cleanly. -/
theorem disjoint_edits_clean (base ours theirs : File Name Body)
    (hdisj : ∀ n, ¬ (changed base ours n ∧ changed base theirs n)) :
    ∀ n, (mergeFile base ours theirs n).isConflict = false := by
  intro n
  have h := hdisj n
  unfold changed at h
  cases hc : (mergeFile base ours theirs n).isConflict
  · rfl
  · have := (decide_conflict_iff (base n) (ours n) (theirs n)).mp hc
    exact absurd ⟨this.1, this.2.1⟩ h

/-- …and the result is exactly "base, with each side's changes applied". -/
theorem disjoint_edits_result (base ours theirs : File Name Body)
    (hdisj : ∀ n, ¬ (changed base ours n ∧ changed base theirs n)) (n : Name) :
    mergeFile base ours theirs n =
      .clean (if ours n ≠ base n then ours n else theirs n) := by
  have h := hdisj n
  unfold changed at h
  unfold mergeFile
  by_cases ho : ours n = base n
  · rw [ho, decide_ours_untouched]; simp
  · have ht : theirs n = base n := Classical.byContradiction fun ht => h ⟨ho, ht⟩
    rw [ht, decide_theirs_untouched]; simp [ho]

/-- File-level symmetry. -/
theorem mergeFile_swap (base ours theirs : File Name Body) (n : Name) :
    mergeFile base ours theirs n = (mergeFile base theirs ours n).swap :=
  decide_swap _ _ _

end Weave
