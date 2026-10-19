/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Trace.Perfect
import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# Shifts of actual perfect complexes and their traces

The native cochain shift and the localization functor's shift comparison
produce a genuine bounded finite-projective model of a shifted perfect
object. Reindexing the finite alternating sum gives its sign, and actual
chain representatives extend this computation to every derived endomorphism.
-/

noncomputable section

universe u v w

open CategoryTheory

namespace EtaleCohomology

variable (R : Type u) [CommRing R]

section Complex

variable (C : CochainComplex (ModuleCat.{v} R) ℤ)

/-- The native shift has the finite modules of the original complex as its terms. -/
instance shiftedComplex_finite [∀ i : ℤ, Module.Finite R (C.X i)] (n i : ℤ) :
    Module.Finite R ((C⟦n⟧).X i) :=
  inferInstanceAs (Module.Finite R (C.X (i + n)))

/-- The native shift has the projective modules of the original complex as its terms. -/
instance shiftedComplex_projective [∀ i : ℤ, Module.Projective R (C.X i)] (n i : ℤ) :
    Module.Projective R ((C⟦n⟧).X i) :=
  inferInstanceAs (Module.Projective R (C.X (i + n)))

/-- The native cochain shift translates a strict lower bound. -/
instance shiftedComplex_boundedBelow (a n : ℤ) [C.IsStrictlyGE a] :
    (C⟦n⟧).IsStrictlyGE (a - n) :=
  C.isStrictlyGE_shift a n (a - n) (by omega)

/-- The native cochain shift translates a strict upper bound. -/
instance shiftedComplex_boundedAbove (b n : ℤ) [C.IsStrictlyLE b] :
    (C⟦n⟧).IsStrictlyLE (b - n) :=
  C.isStrictlyLE_shift b n (b - n) (by omega)

variable [∀ i : ℤ, Module.Finite R (C.X i)]
  [∀ i : ℤ, Module.Projective R (C.X i)]

/-- Shifting a bounded finite-projective complex multiplies its alternating
trace by the parity sign of the shift. -/
theorem boundedComplexTrace_shift
    (a b : ℤ) [C.IsStrictlyGE a] [C.IsStrictlyLE b]
    (n : ℤ) (f : C ⟶ C) :
    boundedComplexTrace R (C⟦n⟧) (a - n) (b - n) (f⟦n⟧') =
      n.negOnePow • boundedComplexTrace R C a b f := by
  let t : ℤ → R := fun i => i.negOnePow •
    LinearMap.projectiveTrace R (C.X i) (f.f i).hom
  have ht : Function.HasFiniteSupport t := signedTrace_hasFiniteSupport R C a b f.f
  have hs : Function.HasFiniteSupport (fun i : ℤ => t (i + n)) :=
    ht.fun_comp_of_injective (Equiv.addRight n).injective
  have hsign (i : ℤ) : n.negOnePow * (i + n).negOnePow = i.negOnePow := by
    rw [mul_comm, ← Int.negOnePow_sub]
    congr 1
    omega
  have hshift (i : ℤ) :
      i.negOnePow • LinearMap.projectiveTrace R (C.X (i + n)) (f.f (i + n)).hom =
        n.negOnePow • t (i + n) := by
    dsimp only [t]
    rw [smul_smul, hsign]
  have hsum : (∑ᶠ i : ℤ, t (i + n)) = ∑ᶠ i : ℤ, t i :=
    finsum_comp_equiv (Equiv.addRight n) (f := t)
  change (∑ᶠ i : ℤ, i.negOnePow •
    LinearMap.projectiveTrace R (C.X (i + n)) (f.f (i + n)).hom) =
      n.negOnePow • ∑ᶠ i : ℤ, t i
  rw [finsum_congr hshift, ← smul_finsum' n.negOnePow hs, hsum]

end Complex

variable [HasDerivedCategory.{w} (ModuleCat.{v} R)]

namespace PerfectComplexModel

variable {R} {K : DerivedCategory (ModuleCat.{v} R)}

/-- A native shift of a genuine model represents the shifted derived object. -/
def shift (P : PerfectComplexModel R K) (n : ℤ) : PerfectComplexModel R (K⟦n⟧) where
  complex := P.complex⟦n⟧
  lower := P.lower - n
  upper := P.upper - n
  finite := fun i => inferInstanceAs (Module.Finite R (P.complex.X (i + n)))
  projective := fun i => inferInstanceAs (Module.Projective R (P.complex.X (i + n)))
  boundedBelow := P.complex.isStrictlyGE_shift P.lower n (P.lower - n) (by omega)
  boundedAbove := P.complex.isStrictlyLE_shift P.upper n (P.upper - n) (by omega)
  iso := (DerivedCategory.Q.commShiftIso n).app P.complex ≪≫
    (shiftFunctor _ n).mapIso P.iso

/-- The representing isomorphism of a shifted model intertwines the actual
localized chain map with the shift of its original derived endomorphism. -/
theorem shift_iso_conjugate_map (P : PerfectComplexModel R K) (n : ℤ)
    (f : P.complex ⟶ P.complex) :
    (P.shift n).iso.inv ≫ DerivedCategory.Q.map (f⟦n⟧') ≫ (P.shift n).iso.hom =
      (P.iso.inv ≫ DerivedCategory.Q.map f ≫ P.iso.hom)⟦n⟧' := by
  dsimp only [shift, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv]
  simp only [Functor.map_comp, Category.assoc, Iso.app_hom, Iso.app_inv,
    Functor.commShiftIso_hom_naturality_assoc, Iso.inv_hom_id_app_assoc]

/-- The parity rule holds for every derived endomorphism, using its actual
chain representative in the chosen bounded projective model. -/
theorem trace_shift (P : PerfectComplexModel R K) (n : ℤ) (f : K ⟶ K) :
    (P.shift n).trace (f⟦n⟧') = n.negOnePow • P.trace f := by
  obtain ⟨g, rfl⟩ := P.exists_chainMap f
  let g' : (P.shift n).complex ⟶ (P.shift n).complex := g⟦n⟧'
  have hconj : (P.shift n).iso.inv ≫ DerivedCategory.Q.map g' ≫ (P.shift n).iso.hom =
      (P.iso.inv ≫ DerivedCategory.Q.map g ≫ P.iso.hom)⟦n⟧' :=
    P.shift_iso_conjugate_map n g
  rw [← hconj, (P.shift n).trace_map g', P.trace_map g]
  exact boundedComplexTrace_shift R P.complex P.lower P.upper n g

end PerfectComplexModel

/-- Every actual shift of a perfect derived object is perfect. -/
theorem isPerfectComplex_shift {K : DerivedCategory (ModuleCat.{v} R)}
    (hK : IsPerfectComplex R K) (n : ℤ) : IsPerfectComplex R (K⟦n⟧) :=
  ⟨(Classical.choice hK).shift n⟩

/-- The intrinsic trace of a shifted derived endomorphism has the parity sign. -/
theorem perfectComplexTrace_shift {K : DerivedCategory (ModuleCat.{v} R)}
    (hK : IsPerfectComplex R K) (n : ℤ) (f : K ⟶ K) :
    perfectComplexTrace R (K⟦n⟧) (isPerfectComplex_shift R hK n) (f⟦n⟧') =
      n.negOnePow • perfectComplexTrace R K hK f := by
  let P := Classical.choice hK
  rw [perfectComplexTrace_eq_modelTrace R (K⟦n⟧) _ (P.shift n),
    perfectComplexTrace_eq_modelTrace R K hK P]
  exact P.trace_shift n f

end EtaleCohomology
