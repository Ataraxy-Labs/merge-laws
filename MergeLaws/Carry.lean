/-!
# land's carry-over: when an earlier test result may be reused

While a test command runs, land records every file it reads (its read-set).
A later version reuses the recorded verdict when every file in that read-set is
unchanged, instead of running the command again.

The assumption that makes this sound is that the command is hermetic: its verdict
depends only on the files it reads. land enforces the parts it can (an offline
microVM, a recorded read-set) and refuses a test that fails and then passes on the
same code, because a run like that is evidence the assumption broke.
-/

namespace Land

variable {Path Content Verdict : Type}

/-- A repository snapshot: every path's content. -/
abbrev Snapshot (Path Content : Type) := Path → Content

/-- A test command with the read-set land recorded for it. -/
structure Test (Path Content Verdict : Type) where
  run   : Snapshot Path Content → Verdict
  reads : Path → Prop

/-- Hermetic: two snapshots that agree on every file the test reads give the same verdict. -/
def Hermetic (t : Test Path Content Verdict) : Prop :=
  ∀ s₁ s₂ : Snapshot Path Content, (∀ p, t.reads p → s₁ p = s₂ p) → t.run s₁ = t.run s₂

/-- A recorded result: the snapshot it ran on and the verdict it produced there. -/
structure Memo (Path Content Verdict : Type) where
  ranOn   : Snapshot Path Content
  verdict : Verdict

/-- land's lookup rule: reuse when nothing the test read has changed. -/
def mayReuse (t : Test Path Content Verdict) (m : Memo Path Content Verdict)
    (now : Snapshot Path Content) : Prop :=
  ∀ p, t.reads p → m.ranOn p = now p

/-- **Soundness of carry-over.** For a hermetic test, a memo recorded honestly and reused
by land's rule gives exactly the verdict a fresh run would give now. -/
theorem carry_sound (t : Test Path Content Verdict) (m : Memo Path Content Verdict)
    (now : Snapshot Path Content)
    (herm : Hermetic t) (honest : m.verdict = t.run m.ranOn) (reuse : mayReuse t m now) :
    m.verdict = t.run now := by
  rw [honest]; exact herm _ _ reuse

/-- Unrelated-change invariance: editing files outside a test's read-set never changes
its verdict, so land never needs to rerun it for that edit. -/
theorem unrelated_change (t : Test Path Content Verdict) (herm : Hermetic t)
    (s : Snapshot Path Content) (edit : Snapshot Path Content)
    (outside : ∀ p, t.reads p → edit p = s p) :
    t.run edit = t.run s :=
  herm _ _ outside

end Land
