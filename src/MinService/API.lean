import Mathlib.Tactic
import Contracts.SortService
import Contracts.MinService

/-! The min service: its implementation, which calls the sort service through the contract in
`Contracts.SortService`, and the proof that it meets its own in `Contracts.MinService`. -/
