/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Classical.FieldHilbert90EtaleObjects
import Nyll.EtaleCohomology.Classical.KummerSequence
import Nyll.EtaleCohomology.Classical.CohomologyPresheafBoundary
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Nyll.SchemeTheory.CategoryTheory.FunctorCategoryExactness

/-!
# The natural Kummer cokernel on a field's small étale site

Geometric Hilbert 90 at every étale object makes the actual Kummer
boundary surjective. Its existing naturality and exact kernel identify the
full cohomology presheaf with the cokernel presheaf, not merely its values at
field spectra.
-/

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits Opposite
open CategoryTheory.Abelian

namespace EtaleCohomology

/-- The existing actual Kummer boundary as an additive homomorphism. -/
def etaleKummerBoundaryAddHom (X : Scheme.{u}) {n : ℕ} (hn : 0 < n)
    (hnX : IsUnit (n : Γ(X, ⊤))) (V : X.Etale) :
    (etaleMultiplicativeGroupSheaf X).obj.obj (op V) →+
    Sheaf.H'.{u} (etaleRootsOfUnitySheaf X n) 1 V :=
  cohomologyPresheafSectionBoundary X (etaleKummerComplex X n)
    (etaleKummerComplex_shortExact X hn hnX) V

/-- The boundary respects the actual cohomology-presheaf restriction maps. -/
def etaleKummerBoundaryPresheafHom (X : Scheme.{u}) {n : ℕ} (hn : 0 < n)
    (hnX : IsUnit (n : Γ(X, ⊤))) :
    (etaleMultiplicativeGroupSheaf X).obj ⟶
      (etaleRootsOfUnitySheaf X n).cohomologyPresheaf 1 :=
  cohomologyPresheafBoundaryHom X (etaleKummerComplex X n)
    (etaleKummerComplex_shortExact X hn hnX)

/-- Hilbert 90 makes the boundary surjective at every étale object over a field. -/
theorem etaleKummerBoundary_surjective_at_etale_object_of_field
    (K : Type u) [Field K] [CharZero K] {n : ℕ} (hn : 0 < n)
    (hnK : IsUnit (n : Γ(Spec (.of K), ⊤))) (V : (Spec (.of K)).Etale) :
    Function.Surjective (etaleKummerBoundary (Spec (.of K)) hn hnK V) := by
  intro a
  let X := Spec (.of K)
  let M := etaleMultiplicativeGroupSheaf X
  let P := (freeAbelianSheafYoneda X.smallEtaleTopology).obj V
  let E : (P ⟶ M) ≃ M.obj.obj (op V) :=
    freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology V M
  have hS := etaleKummerComplex_shortExact X hn hnK
  obtain ⟨b, hb⟩ := Ext.covariant_sequence_exact₁ P hS a
    (etaleMultiplicativeGroup_H1_eq_zero_at_etale_object_of_field K V _) (n₀ := 0) rfl
  obtain ⟨f, hf⟩ := (Ext.mk₀_bijective P M).surjective b
  refine ⟨E f, ?_⟩
  change (Ext.mk₀ (E.symm (E f))).comp hS.extClass (zero_add 1) = a
  rw [E.symm_apply_apply, hf]
  exact hb

/-- The complete actual Kummer H1 presheaf over a characteristic-zero field
is the cokernel of the unit power map as a presheaf. -/
def etaleKummerPresheafCokernelIso_of_field
    (K : Type u) [Field K] [CharZero K] {n : ℕ} (hn : 0 < n)
    (hnK : IsUnit (n : Γ(Spec (.of K), ⊤))) :
    cokernel ((etaleMultiplicativeGroupPower (Spec (.of K)) n).hom) ≅
      (etaleRootsOfUnitySheaf (Spec (.of K)) n).cohomologyPresheaf 1 := by
  let X := Spec (.of K)
  let f := (etaleMultiplicativeGroupPower X n).hom
  let g := etaleKummerBoundaryPresheafHom X hn hnK
  refine CategoryTheory.presheafCokernelIsoOfExact f g ?_ ?_ ?_
  · apply NatTrans.ext
    funext V
    apply ConcreteCategory.hom_ext
    intro s
    exact (etaleKummerBoundary_eq_zero_iff X hn hnK V.unop (f.app V s)).mpr ⟨s, rfl⟩
  · intro V s hs
    exact (etaleKummerBoundary_eq_zero_iff X hn hnK V.unop s).mp hs
  · intro V
    exact etaleKummerBoundary_surjective_at_etale_object_of_field K hn hnK V.unop

end EtaleCohomology
