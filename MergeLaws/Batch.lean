import MergeLaws.Carry

/-!
# Landing changes together

land can check several branches in one run instead of one after another. These theorems say
when that is safe, in the same model as `Carry.lean`: a change writes some paths, and a test's
verdict depends only on the paths it reads.

* two changes that write different paths commute: either order gives the same repository
* a change that writes nothing a test reads cannot move that test's verdict, so a verdict
  checked for one change still holds when an unrelated change lands beside it
* adding an unrelated change to a batch cannot turn a refusal into a landing
-/

namespace Land

variable {Path Content Verdict : Type}

/-- A change: which paths it writes, and what it writes there. -/
structure Change (Path Content : Type) where
  writes : Path → Bool
  new    : Path → Content

/-- Apply a change to a snapshot. -/
def Change.apply (c : Change Path Content) (s : Snapshot Path Content) : Snapshot Path Content :=
  fun p => if c.writes p then c.new p else s p

/-- Two changes that never write the same path. -/
def Disjoint (c d : Change Path Content) : Prop := ∀ p, ¬ (c.writes p = true ∧ d.writes p = true)

/-- A change writes nothing a test reads. -/
def Untouched (t : Test Path Content Verdict) (d : Change Path Content) : Prop :=
  ∀ p, t.reads p → d.writes p = false

/-- A path a change does not write keeps its content. -/
theorem apply_outside (c : Change Path Content) (s : Snapshot Path Content) (p : Path)
    (h : c.writes p = false) : c.apply s p = s p := by
  simp [Change.apply, h]

/-- **Order does not matter.** Two changes that write different paths give the same repository
whichever lands first. -/
theorem apply_comm (c d : Change Path Content) (h : Disjoint c d) (s : Snapshot Path Content) :
    c.apply (d.apply s) = d.apply (c.apply s) := by
  funext p
  unfold Change.apply
  cases hc : c.writes p <;> cases hd : d.writes p <;> simp
  exact absurd ⟨hc, hd⟩ (h p)

/-- **A batch keeps each verdict.** If change `d` writes nothing test `t` reads, then `t`'s verdict
with `c` and `d` landed together is the verdict `t` had with `c` alone. -/
theorem batch_keeps_verdict (t : Test Path Content Verdict) (herm : Hermetic t)
    (c d : Change Path Content) (h : Untouched t d) (s : Snapshot Path Content) :
    t.run (d.apply (c.apply s)) = t.run (c.apply s) :=
  herm _ _ fun p hp => apply_outside d _ p (h p hp)

/-- The same verdict whichever change is applied first, when they write different paths. -/
theorem verdict_order_free (t : Test Path Content Verdict) (c d : Change Path Content)
    (h : Disjoint c d) (s : Snapshot Path Content) :
    t.run (c.apply (d.apply s)) = t.run (d.apply (c.apply s)) := by
  rw [apply_comm c d h s]

/-- **Refusal monotonicity.** A test that fails for change `c` still fails when an unrelated change
`d` joins the batch: batching never lets a broken change through. -/
theorem refusal_monotone (t : Test Path Content Bool) (herm : Hermetic t)
    (c d : Change Path Content) (h : Untouched t d) (s : Snapshot Path Content)
    (fails : t.run (c.apply s) = false) :
    t.run (d.apply (c.apply s)) = false := by
  rw [batch_keeps_verdict t herm c d h s]; exact fails

/-- …and likewise a pass stays a pass: checking `c` once is enough for the batch, for every test
the other change does not touch. -/
theorem pass_monotone (t : Test Path Content Bool) (herm : Hermetic t)
    (c d : Change Path Content) (h : Untouched t d) (s : Snapshot Path Content)
    (passes : t.run (c.apply s) = true) :
    t.run (d.apply (c.apply s)) = true := by
  rw [batch_keeps_verdict t herm c d h s]; exact passes

end Land
