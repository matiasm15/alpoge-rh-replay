import Mathlib
open Function
/-! At the replay's Mathlib pin, `MultilinearMap R M N` was the structure with fields `toFun`,
`map_update_add'` and `map_update_smul' : toFun (update m i (c • x)) = c • toFun (update m i x)`.
On the target, a function underlies a `MultilinearMap (RingHom.id R) M N` exactly when it satisfies
those same two conditions, and the structure is determined by the function. -/
theorem multilinear_id_iff_old {R ι N : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [AddCommMonoid N] [∀ i, Module R (M i)] [Module R N]
    (f : (∀ i, M i) → N) :
    (∃ g : MultilinearMap (RingHom.id R) M N, ⇑g = f) ↔
      ((∀ [DecidableEq ι] (m : ∀ i, M i) (i : ι) (x y : M i),
          f (update m i (x + y)) = f (update m i x) + f (update m i y)) ∧
       (∀ [DecidableEq ι] (m : ∀ i, M i) (i : ι) (c : R) (x : M i),
          f (update m i (c • x)) = c • f (update m i x))) :=
  ⟨fun ⟨g, hg⟩ => hg ▸ ⟨fun m i x y => g.map_update_add' m i x y,
      fun m i c x => g.map_update_smul' m i c x⟩,
   fun ⟨h1, h2⟩ => ⟨⟨f, h1, h2⟩, rfl⟩⟩

theorem multilinear_id_ext {R ι N : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [AddCommMonoid N] [∀ i, Module R (M i)] [Module R N]
    {g g' : MultilinearMap (RingHom.id R) M N} (h : ⇑g = ⇑g') : g = g' :=
  DFunLike.coe_injective h

#print axioms multilinear_id_iff_old
#print axioms multilinear_id_ext
