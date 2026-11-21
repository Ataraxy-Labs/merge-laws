import Lake
open Lake DSL

package «merge-laws» where

@[default_target]
lean_lib MergeLaws where

/-- Prints random three-way merges with the model's expected outcome, for the differential test. -/
lean_exe gencases where
  root := `GenCases
