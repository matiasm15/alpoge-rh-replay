import Mathlib
/-! At the replay's Mathlib pin, `Submodule.IsLattice K M` was the structure with fields
`fg : M.FG` and `span_eq_top : span K M = ⊤`. On the target, over a fraction field,
`Submodule.IsFullLattice K M` is equivalent to exactly those two conditions. -/
theorem isFullLattice_iff_old {R K V : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    (M : Submodule R V) :
    Submodule.IsFullLattice K M ↔ (M.FG ∧ Submodule.span K (M : Set V) = ⊤) :=
  ⟨fun h => ⟨h.fg, h.span_eq_top⟩,
   fun h => { toIsLattice := Submodule.IsLattice.of_fg K h.1, span_eq_top := h.2 }⟩

open NumberField in
example (E : Type) [Field E] [NumberField E] : IsFractionRing (𝓞 E) E := inferInstance
#print axioms isFullLattice_iff_old
