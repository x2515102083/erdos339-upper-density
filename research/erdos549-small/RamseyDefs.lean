/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    https://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

The two definitions below are reproduced without mathematical changes from
FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Ramsey.lean at
https://github.com/google-deepmind/formal-conjectures/tree/d5ba143cc2fafd48cc6d5b6320a3aab287c38df7
Only imports and this explanatory notice differ. No proof of Erdos 549 is
imported. IsContained is Mathlib's non-induced injective-homomorphism predicate.
-/
import Mathlib

namespace SimpleGraph

noncomputable def graphRamsey {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) : ℕ :=
  sInf { n : ℕ | ∀ (C : SimpleGraph (Fin n)), G.IsContained C ∨ H.IsContained Cᶜ }

noncomputable def diagonalGraphRamsey {α : Type*} [Fintype α] (G : SimpleGraph α) : ℕ :=
  graphRamsey G G

end SimpleGraph
