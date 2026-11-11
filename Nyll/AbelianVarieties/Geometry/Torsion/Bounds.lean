/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.Algebra.MonoidAlgebra.Lift
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Lean.Elab.Tactic.Omega
public import Nyll.AbelianVarieties.Geometry.AffineHopfAlgebra
public import Nyll.AbelianVarieties.Geometry.ProperSubgroups
public import Nyll.AbelianVarieties.Geometry.Torsion.Degree
public import Nyll.AbelianVarieties.Reduction.TorsionSpecialization
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver
public import Nyll.SchemeTheory.Etale.Neighborhoods
public import Nyll.SchemeTheory.GroupSchemes.HopfAlgebra.GroupLike
public import Nyll.AbelianVarieties.Basic
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.BaseChange
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Kernel
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.EndDegree
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.GeometricallyConnectedIdentityComponent
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.IrreducibleIdentityComponentIndex

/-!
# Bounds for prime-to-characteristic torsion

Bound torsion in connected affine groups by their character rank, then combine the
proper quotient and finitely many components to obtain the nonproper torsion bound.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_finite_and_natCard_isTorsionPoint_le_pow_of_isAffine.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.AffineTorsionBounds

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open WithConv

universe u

namespace CharacterRestriction

section PointGroup

variable {k : Type u} [CommRing k]
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))

theorem equiv_one {W : Type*} [Monoid W] (e : W ≃ SchemeHomOver t f)
    (he : ∀ φ ψ : W, e (φ * ψ) = L.mul t (e φ) (e ψ)) : e 1 = L.one t := by
  have h1 : L.mul t (e 1) (e 1) = e 1 := by rw [← he, one_mul]
  calc e 1 = L.mul t (L.inv t (e 1)) (L.mul t (e 1) (e 1)) := by
          rw [← L.mul_assoc, L.inv_mul_cancel, L.one_mul]
    _ = L.one t := by rw [h1, L.inv_mul_cancel]

theorem equiv_pow {W : Type*} [Monoid W] (e : W ≃ SchemeHomOver t f)
    (he : ∀ φ ψ : W, e (φ * ψ) = L.mul t (e φ) (e ψ)) (n : ℕ) (φ : W) :
    e (φ ^ n) = L.nsmul t n (e φ) := by
  induction n with
  | zero => rw [pow_zero, L.nsmul_zero, equiv_one L t e he]
  | succ n ih => rw [pow_succ, he, ih, L.nsmul_succ]

/-- Transport finite-order points along a multiplicative equivalence. -/
def torsionEquiv {W : Type*} [Monoid W] (e : W ≃ SchemeHomOver t f)
    (he : ∀ φ ψ : W, e (φ * ψ) = L.mul t (e φ) (e ψ)) (n : ℕ) :
    {φ : W // φ ^ n = 1} ≃ {x : SchemeHomOver t f // L.IsTorsionPoint t n x} :=
  e.subtypeEquiv fun φ => by
    rw [L.isTorsionPoint_def, ← equiv_pow L t e he, ← equiv_one L t e he]
    exact e.injective.eq_iff.symm

theorem transport {t t' : T ⟶ Spec (CommRingCat.of k)} (htt : t = t') (n B : ℕ)
    (H : Finite {x : SchemeHomOver t f // L.IsTorsionPoint t n x} ∧
      Nat.card {x : SchemeHomOver t f // L.IsTorsionPoint t n x} ≤ B) :
    Finite {x : SchemeHomOver t' f // L.IsTorsionPoint t' n x} ∧
      Nat.card {x : SchemeHomOver t' f // L.IsTorsionPoint t' n x} ≤ B := by
  subst htt
  exact H

end PointGroup

section Hopf

variable (k : Type u) [Field k] (H : Type u) [CommRing H] [HopfAlgebra k H]

/-- The additive character lattice of the commutative Hopf algebra. -/
abbrev CharLat : Type u := Additive (GroupLike k H)

/-- Include the character lattice as group-like elements. -/
noncomputable def inclHom : Multiplicative (CharLat k H) →* H where
  toFun x := (Additive.toMul (Multiplicative.toAdd x) : GroupLike k H).val
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The algebra map generated by the group-like elements. -/
noncomputable def res : AddMonoidAlgebra k (CharLat k H) →ₐ[k] H :=
  AddMonoidAlgebra.lift k H (CharLat k H) (inclHom k H)

variable {k H}

theorem res_single (g : GroupLike k H) (c : k) :
    res k H (AddMonoidAlgebra.single (Additive.ofMul g) c) = c • g.val := by
  rw [res, AddMonoidAlgebra.lift_single]
  rfl

theorem convMul_apply_of_isGroupLikeElem (φ ψ : WithConv (H →ₐ[k] k)) {g : H}
    (hg : IsGroupLikeElem k g) : (φ * ψ) g = φ g * ψ g := by
  rw [AlgHom.convMul_apply, hg.comul_eq_tmul_self, Algebra.TensorProduct.lift_tmul]

theorem convOne_apply_of_isGroupLikeElem {g : H} (hg : IsGroupLikeElem k g) :
    (1 : WithConv (H →ₐ[k] k)) g = 1 := by
  rw [AlgHom.convOne_apply, hg.counit_eq_one, map_one]

theorem convPow_apply_of_isGroupLikeElem (φ : WithConv (H →ₐ[k] k)) {g : H}
    (hg : IsGroupLikeElem k g) (n : ℕ) : (φ ^ n) g = (φ g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, convOne_apply_of_isGroupLikeElem hg]
  | succ n ih => rw [pow_succ, convMul_apply_of_isGroupLikeElem _ _ hg, ih, pow_succ]

/-- Restrict a convolution character to the group-like subalgebra. -/
noncomputable def resPt (φ : WithConv (H →ₐ[k] k)) :
    WithConv (AddMonoidAlgebra k (CharLat k H) →ₐ[k] k) :=
  toConv (φ.ofConv.comp (res k H))

theorem resPt_single (φ : WithConv (H →ₐ[k] k)) (g : GroupLike k H) :
    resPt φ (AddMonoidAlgebra.single (Additive.ofMul g) 1) = φ g.val := by
  change φ.ofConv (res k H (AddMonoidAlgebra.single (Additive.ofMul g) 1)) = _
  rw [res_single, one_smul]

theorem comul_single_one (g : GroupLike k H) :
    Coalgebra.comul (R := k) (AddMonoidAlgebra.single (Additive.ofMul g) (1 : k)) =
      AddMonoidAlgebra.single (Additive.ofMul g) (1 : k) ⊗ₜ[k]
        AddMonoidAlgebra.single (Additive.ofMul g) (1 : k) := by
  rw [AddMonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul]
  rfl

theorem counit_single_one (g : GroupLike k H) :
    Coalgebra.counit (R := k) (AddMonoidAlgebra.single (Additive.ofMul g) (1 : k)) = 1 := by
  rw [AddMonoidAlgebra.counit_single]
  rfl

theorem resPt_mul (φ ψ : WithConv (H →ₐ[k] k)) : resPt (φ * ψ) = resPt φ * resPt ψ := by
  apply WithConv.ofConv_injective
  refine AddMonoidAlgebra.algHom_ext (fun a => ?_) (Subsingleton.elim _ _)
  change resPt (φ * ψ) (AddMonoidAlgebra.single a 1) = (resPt φ * resPt ψ)
    (AddMonoidAlgebra.single a 1)
  obtain ⟨g, rfl⟩ : ∃ g : GroupLike k H, Additive.ofMul g = a := ⟨Additive.toMul a, rfl⟩
  rw [resPt_single, convMul_apply_of_isGroupLikeElem _ _ g.2, AlgHom.convMul_apply,
    comul_single_one, Algebra.TensorProduct.lift_tmul]
  change _ = resPt φ _ * resPt ψ _
  rw [resPt_single, resPt_single]

theorem resPt_one : resPt (1 : WithConv (H →ₐ[k] k)) = 1 := by
  apply WithConv.ofConv_injective
  refine AddMonoidAlgebra.algHom_ext (fun a => ?_) (Subsingleton.elim _ _)
  change resPt (1 : WithConv (H →ₐ[k] k)) (AddMonoidAlgebra.single a 1) =
    (1 : WithConv (AddMonoidAlgebra k (CharLat k H) →ₐ[k] k)) (AddMonoidAlgebra.single a 1)
  obtain ⟨g, rfl⟩ : ∃ g : GroupLike k H, Additive.ofMul g = a := ⟨Additive.toMul a, rfl⟩
  rw [resPt_single, convOne_apply_of_isGroupLikeElem g.2, AlgHom.convOne_apply, counit_single_one,
    map_one]

theorem resPt_pow (φ : WithConv (H →ₐ[k] k)) (n : ℕ) : resPt (φ ^ n) = resPt φ ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, resPt_one]
  | succ n ih => rw [pow_succ, resPt_mul, ih, pow_succ]

theorem eq_of_resPt_eq [IsAlgClosed k] [Coalgebra.IsCocomm k H] {m : ℕ} (hm : (m : k) ≠ 0)
    {φ ψ : WithConv (H →ₐ[k] k)} (hφ : φ ^ m = 1) (hψ : ψ ^ m = 1)
    (hres : resPt φ = resPt ψ) : φ = ψ := by
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exact absurd (by rw [h0, Nat.cast_zero]) hm
    · exact h0
  let χ : WithConv (H →ₐ[k] k) := ψ * φ ^ (m - 1)
  have hχm : χ ^ m = 1 := by
    change (ψ * φ ^ (m - 1)) ^ m = 1
    rw [mul_pow, hψ, one_mul, ← pow_mul, mul_comm, pow_mul, hφ, one_pow]
  have hval : ∀ g : H, IsGroupLikeElem k g → φ g = ψ g := by
    intro g hg
    have := congrArg (fun χ => χ (AddMonoidAlgebra.single (Additive.ofMul (⟨g, hg⟩ : GroupLike k
      H)) 1))
      hres
    simpa only [resPt_single] using this
  have hχ1 : ∀ g : H, IsGroupLikeElem k g → χ g = 1 := by
    intro g hg
    change (ψ * φ ^ (m - 1)) g = 1
    rw [convMul_apply_of_isGroupLikeElem _ _ hg, convPow_apply_of_isGroupLikeElem _ hg, ← hval g hg,
      ← pow_succ', Nat.sub_add_cancel hm1, ← convPow_apply_of_isGroupLikeElem _ hg, hφ,
      convOne_apply_of_isGroupLikeElem hg]
  have hχ : χ = 1 :=
    HopfAlgebra.withConv_algHom_eq_one_of_pow_eq_one_of_forall_isGroupLikeElem k H χ m hm hχm hχ1
  calc φ = χ * φ := by rw [hχ, one_mul]
    _ = ψ * φ ^ (m - 1 + 1) := by
        change ψ * φ ^ (m - 1) * φ = _
        rw [pow_succ, mul_assoc]
    _ = ψ := by rw [Nat.sub_add_cancel hm1, hφ, mul_one]

theorem finite_and_natCard_le [IsAlgClosed k] [Coalgebra.IsCocomm k H]
    [ConnectedSpace (PrimeSpectrum H)] (h : ℕ)
    (hsm : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension h) (algebraMap k H))
    (m : ℕ) (hm : (m : k) ≠ 0) :
    Finite {φ : WithConv (H →ₐ[k] k) // φ ^ m = 1} ∧
      Nat.card {φ : WithConv (H →ₐ[k] k) // φ ^ m = 1} ≤ m ^ h := by
  obtain ⟨hfree, hfin, hrank⟩ := (open HopfAlgebra in
    free_and_finite_and_finrank_groupLike_le_of_locally_isStandardSmoothOfRelativeDimension
      k H h hsm)
  have : NeZero (m : k) := ⟨hm⟩
  have : NeZero m := NeZero.of_neZero_natCast k
  have hT := AddMonoidAlgebra.natCard_withConv_algHom_pow_eq_one k (CharLat k H) k m
  let ι : {φ : WithConv (H →ₐ[k] k) // φ ^ m = 1} →
      {χ : WithConv (AddMonoidAlgebra k (CharLat k H) →ₐ[k] k) // χ ^ m = 1} :=
    fun φ => ⟨resPt φ.1, by rw [← resPt_pow, φ.2, resPt_one]⟩
  have hι : Function.Injective ι := by
    intro φ ψ hφψ
    apply Subtype.ext
    exact eq_of_resPt_eq hm φ.2 ψ.2 (congrArg Subtype.val hφψ)
  have hm1 : 1 ≤ m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hfinT : Finite {χ : WithConv (AddMonoidAlgebra k (CharLat k H) →ₐ[k] k) // χ ^ m = 1} := by
    apply Nat.finite_of_card_ne_zero
    rw [hT]
    exact pow_ne_zero _ (NeZero.ne m)
  refine ⟨Finite.of_injective ι hι, ?_⟩
  calc Nat.card {φ : WithConv (H →ₐ[k] k) // φ ^ m = 1}
      ≤ Nat.card {χ : WithConv (AddMonoidAlgebra k (CharLat k H) →ₐ[k] k) // χ ^ m = 1} :=
        Nat.card_le_card_of_injective ι hι
    _ = m ^ Module.finrank ℤ (CharLat k H) := hT
    _ ≤ m ^ h := Nat.pow_le_pow_right hm1 hrank

end Hopf

section SchemeSide

variable (k : Type u) [Field k] {N : Scheme.{u}} (f : N ⟶ Spec (CommRingCat.of k))

theorem specMap_algebraMap_self :
    Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (Spec (CommRingCat.of k)) := by
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id]
  exact Spec.map_id _

theorem connectedSpace_primeSpectrum_of_iso [ConnectedSpace N] (H : Type u) [CommRing H]
    (I : N ≅ Spec (CommRingCat.of H)) : ConnectedSpace (PrimeSpectrum H) := by
  let e := Scheme.homeoOfIso I
  exact e.surjective.connectedSpace e.continuous

theorem locally_isStandardSmoothOfRelativeDimension_of_algEquiv [IsAffine N] (h : ℕ)
    [SmoothOfRelativeDimension h f] (H : Type u) [CommRing H]
    (algN : Algebra k Γ(N, ⊤))
    (halg : algebraMap k Γ(N, ⊤) = ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom)
    [Algebra k H] (iso : H ≃ₐ[k] Γ(N, ⊤)) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension h) (algebraMap k H) := by
  have hP : RingHom.RespectsIso (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension h)) :=
    RingHom.locally_respectsIso RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  have H1 : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension h) f.appTop.hom :=
    HasRingHomProperty.appTop (P := @SmoothOfRelativeDimension h) f inferInstance
  let e₁ : k ≃+* Γ(Spec (CommRingCat.of k), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm
  have H2 : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension h)
      (f.appTop.hom.comp e₁.toRingHom) := hP.2 _ e₁ H1
  let e₂ : Γ(N, ⊤) ≃+* H := iso.symm.toRingEquiv
  have H3 := hP.1 _ e₂ H2
  have heq : algebraMap k H = e₂.toRingHom.comp (f.appTop.hom.comp e₁.toRingHom) := by
    ext x
    change algebraMap k H x = iso.symm (f.appTop.hom (e₁ x))
    have h1 : algebraMap k H x = iso.symm (algebraMap k Γ(N, ⊤) x) := (iso.symm.commutes x).symm
    rw [h1, halg]
    rfl
  rw [heq]
  exact H3

end SchemeSide

end CharacterRestriction

open CharacterRestriction

end AbelianVarieties.NOSProofs.AffineTorsionBounds

namespace GoodReductionJacobian.RelativeGroupLaw

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian

universe u

open AbelianVarieties.NOSProofs.AffineTorsionBounds.CharacterRestriction

theorem
    finite_and_natCard_isTorsionPoint_le_pow_of_isAffine
    (k : Type u) [Field k] [IsAlgClosed k] {N : Scheme.{u}} [IsAffine N] [ConnectedSpace N]
    (f : N ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    (h : ℕ) [SmoothOfRelativeDimension h f] (m : ℕ) (hm : (m : k) ≠ 0) :
    Finite {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f //
        L.IsTorsionPoint (𝟙 (Spec (CommRingCat.of k))) m x} ∧
      Nat.card {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f //
        L.IsTorsionPoint (𝟙 (Spec (CommRingCat.of k))) m x} ≤ m ^ h := by
  have : Smooth f := SmoothOfRelativeDimension.smooth h f
  have : LocallyOfFiniteType f := inferInstance
  let algN : Algebra k Γ(N, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    f.appTop).hom.toAlgebra
  obtain ⟨H, _instR, _instH, hft, hfl, hcocomm, iso, e, hept, hemul, henat⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_algEquiv_globalSections_of_isAffineHom
      L (fun t x y => hc t x y)
  have : ConnectedSpace (PrimeSpectrum H) := by
    refine connectedSpace_primeSpectrum_of_iso (N := N) H (N.isoSpec ≪≫ ?_)
    exact Scheme.Spec.mapIso (iso.toRingEquiv.toCommRingCatIso).op
  have hsm : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension h) (algebraMap k H) :=
    locally_isStandardSmoothOfRelativeDimension_of_algEquiv k f h H algN rfl iso
  obtain ⟨hfinH, hcardH⟩ := finite_and_natCard_le (k := k) (H := H) h hsm m hm
  apply transport L (specMap_algebraMap_self k) m (m ^ h)
  let E := torsionEquiv L _ (e k) (hemul k) m
  exact ⟨Finite.of_equiv _ E, by rw [← Nat.card_congr E]; exact hcardH⟩

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_isProper_or_natCard_isTorsionPoint_le_pow_sub_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.ConnectedTorsionBounds

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

universe u

namespace TorsionProperReduction
open _root_.GoodReductionJacobian.RelativeGroupLaw
open _root_.GoodReductionJacobian

section PointGroup

variable {k : Type u} [CommRing k]
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))

theorem nsmul_eq_pow (n : ℕ) (x : SchemeHomOver t f) :
    L.nsmul t n x = (let : Group (SchemeHomOver t f) := L.pointGroup t; x ^ n) := by
  let : Group (SchemeHomOver t f) := L.pointGroup t
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [L.nsmul_succ, pow_succ, ih]
      rfl

theorem isTorsionPoint_iff_pow_eq_one (n : ℕ) (x : SchemeHomOver t f) :
    L.IsTorsionPoint t n x ↔
      (let : Group (SchemeHomOver t f) := L.pointGroup t; x ^ n = 1) := by
  rw [L.isTorsionPoint_def, nsmul_eq_pow]
  rfl

end PointGroup

section Abstract

/-- Elements killed by the indicated power map. -/
abbrev Tors (P : Type*) [Group P] (m : ℕ) : Type _ := {x : P // x ^ m = 1}

variable {P Q S : Type*} [CommGroup P] [Group Q] [Group S]

theorem finite_tors_and_natCard_tors_le_mul (ι : S →* P) (hι : Function.Injective ι)
    (π : P →* Q) (hker : ∀ x : P, π x = 1 → ∃ y : S, ι y = x) (m : ℕ)
    [Finite (Tors S m)] [Finite (Tors Q m)] :
    Finite (Tors P m) ∧ Nat.card (Tors P m) ≤ Nat.card (Tors S m) * Nat.card (Tors Q m) := by
  classical
  let TP : Subgroup P := (powMonoidHom m : P →* P).ker
  have hmemTP : ∀ x : P, x ∈ TP ↔ x ^ m = 1 := fun x => by
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
  have eTP : Tors P m ≃ TP := Equiv.subtypeEquivRight (fun x => (hmemTP x).symm)
  have hcardTP : Nat.card (Tors P m) = Nat.card TP := Nat.card_congr eTP
  let π' : TP →* Q := π.comp TP.subtype
  have hsplit : Nat.card TP = Nat.card (TP ⧸ π'.ker) * Nat.card π'.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  let eQ : TP ⧸ π'.ker ≃ π'.range := (QuotientGroup.quotientKerEquivRange π').toEquiv
  let toQ : π'.range → Tors Q m := fun r => ⟨r.1, by
    obtain ⟨x, hx⟩ := r.2
    have hxm : (x : P) ^ m = 1 := (hmemTP x).1 x.2
    rw [← hx]
    change (π (x : P)) ^ m = 1
    rw [← map_pow, hxm, map_one]⟩
  have htoQ : Function.Injective toQ := by
    intro r r' hrr'
    have h1 := Subtype.ext_iff.1 hrr'
    exact Subtype.ext h1
  have hex : ∀ z : π'.ker, ∃ y : S, ι y = ((z : TP) : P) := fun z => by
    refine hker _ ?_
    have hz : π' (z : TP) = 1 := (MonoidHom.mem_ker).1 z.2
    exact hz
  choose lift hlift using hex
  let toS : π'.ker → Tors S m := fun z => ⟨lift z, by
    apply hι
    rw [map_pow, hlift, map_one]
    exact (hmemTP _).1 (z : TP).2⟩
  have htoS : Function.Injective toS := by
    intro z z' hzz'
    have h1 : lift z = lift z' := Subtype.ext_iff.1 hzz'
    apply Subtype.ext
    apply Subtype.ext
    rw [← hlift z, ← hlift z', h1]
  have hfinQ : Finite (TP ⧸ π'.ker) := Finite.of_injective (toQ ∘ eQ) (htoQ.comp eQ.injective)
  have hfinS : Finite π'.ker := Finite.of_injective toS htoS
  have hTPne : Nat.card TP ≠ 0 := by
    rw [hsplit]
    exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'
  have : Finite TP := Nat.finite_of_card_ne_zero hTPne
  refine ⟨Finite.of_equiv _ eTP.symm, ?_⟩
  calc Nat.card (Tors P m) = Nat.card (TP ⧸ π'.ker) * Nat.card π'.ker := by rw [hcardTP, hsplit]
    _ ≤ Nat.card (Tors Q m) * Nat.card (Tors S m) := by
        rw [Nat.card_congr eQ]
        exact Nat.mul_le_mul (Nat.card_le_card_of_injective toQ htoQ)
          (Nat.card_le_card_of_injective toS htoS)
    _ = Nat.card (Tors S m) * Nat.card (Tors Q m) := Nat.mul_comm _ _

end Abstract

theorem main
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G]
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    (g : ℕ) [SmoothOfRelativeDimension g f] :
    IsProper f ∨ ∀ m : ℕ, (m : k) ≠ 0 →
      Finite {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f //
          L.IsTorsionPoint (𝟙 (Spec (CommRingCat.of k))) m x} ∧
        Nat.card {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f //
          L.IsTorsionPoint (𝟙 (Spec (CommRingCat.of k))) m x} ≤ m ^ (2 * g - 1) := by
  by_cases hG : IsProper f
  · exact Or.inl hG
  refine Or.inr fun m hmk => ?_
  obtain ⟨N, i, LN, h, A, fA, LA, a, q, hci, hNaff, hNconn, hNsm, hLNc, hihom, hA, hAsm, hLAc,
    hqhom, -, hker, hgha, hh⟩ :=
    exists_isAffine_isClosedImmersion_abelianSchemePropertyBundle_of_not_isProper
      k f L hc g hG
  obtain ⟨hNfin, hNle⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.finite_and_natCard_isTorsionPoint_le_pow_of_isAffine
      k (i ≫ f) LN hLNc h m hmk
  have hAeq :=
    GoodReductionJacobian.RelativeGroupLaw.natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero
      k fA LA hLAc hA a m hmk
  let instP : CommGroup (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :=
    L.pointCommGroup hc (𝟙 (Spec (CommRingCat.of k)))
  let instS : Group (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (i ≫ f)) :=
    LN.pointGroup (𝟙 (Spec (CommRingCat.of k)))
  let instQ : Group (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) fA) :=
    LA.pointGroup (𝟙 (Spec (CommRingCat.of k)))
  let iPt : SchemeHomOver (i ≫ f) f := ⟨i, rfl⟩
  let ι : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (i ≫ f) →*
      SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f :=
    MonoidHom.mk' (fun y => NeronModelInfra.schemeHomOverComp y iPt)
      (fun x y => hihom (𝟙 (Spec (CommRingCat.of k))) x y)
  let π : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f →*
      SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) fA :=
    MonoidHom.mk' (fun x => NeronModelInfra.schemeHomOverComp x q)
      (fun x y => hqhom (𝟙 (Spec (CommRingCat.of k))) x y)
  have hιinj : Function.Injective ι := by
    intro y y' hyy'
    have hval : y.1 ≫ i = y'.1 ≫ i := congrArg Subtype.val hyy'
    exact Subtype.ext ((cancel_mono i).1 hval)
  have hkerι : ∀ x, π x = 1 → ∃ y, ι y = x := fun x hx =>
    (hker (𝟙 (Spec (CommRingCat.of k))) x).1 hx
  have eP : {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f //
        L.IsTorsionPoint (𝟙 (Spec (CommRingCat.of k))) m x} ≃
      Tors (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) m :=
    Equiv.subtypeEquivRight (fun x => isTorsionPoint_iff_pow_eq_one L _ m x)
  have eS : {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (i ≫ f) //
        LN.IsTorsionPoint (𝟙 (Spec (CommRingCat.of k))) m x} ≃
      Tors (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (i ≫ f)) m :=
    Equiv.subtypeEquivRight (fun x => isTorsionPoint_iff_pow_eq_one LN _ m x)
  have eQ : {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) fA //
        LA.IsTorsionPoint (𝟙 (Spec (CommRingCat.of k))) m x} ≃
      Tors (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) fA) m :=
    Equiv.subtypeEquivRight (fun x => isTorsionPoint_iff_pow_eq_one LA _ m x)
  have : Finite (Tors (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (i ≫ f)) m) :=
    Finite.of_equiv _ eS
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hmk Nat.cast_zero
  have : Finite (Tors (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) fA) m) := by
    have : Finite {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) fA //
        LA.IsTorsionPoint (𝟙 (Spec (CommRingCat.of k))) m x} :=
      Nat.finite_of_card_ne_zero (by rw [hAeq]; exact pow_ne_zero _ hm0)
    exact Finite.of_equiv _ eQ
  obtain ⟨hfinP, key⟩ := finite_tors_and_natCard_tors_le_mul ι hιinj π hkerι m
  rw [← Nat.card_congr eP, ← Nat.card_congr eS, ← Nat.card_congr eQ, hAeq] at key
  refine ⟨Finite.of_equiv _ eP.symm, ?_⟩
  calc _ ≤ _ := key
    _ ≤ m ^ h * m ^ (2 * a) := Nat.mul_le_mul_right _ hNle
    _ = m ^ (h + 2 * a) := (pow_add m h (2 * a)).symm
    _ ≤ m ^ (2 * g - 1) := Nat.pow_le_pow_right (Nat.pos_of_ne_zero hm0) (by omega)

end TorsionProperReduction

end AbelianVarieties.NOSProofs.ConnectedTorsionBounds

namespace GoodReductionJacobian.RelativeGroupLaw

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian

universe u

open AbelianVarieties.NOSProofs.ConnectedTorsionBounds

theorem
    isProper_or_natCard_isTorsionPoint_le_pow_sub_one
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G]
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    (g : ℕ) [SmoothOfRelativeDimension g f] :
    IsProper f ∨ ∀ m : ℕ, (m : k) ≠ 0 →
      Finite {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f //
          L.IsTorsionPoint (𝟙 (Spec (CommRingCat.of k))) m x} ∧
        Nat.card {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f //
          L.IsTorsionPoint (𝟙 (Spec (CommRingCat.of k))) m x} ≤ m ^ (2 * g - 1) :=
  TorsionProperReduction.main k f L hc g

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_forall_isProper_or_exists_natCard_isTorsionPoint_le_mul_pow.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.TorsionBounds

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace ComponentCount

open AbelianVarieties.NOSProofs.ConnectedTorsionBounds.TorsionProperReduction
  (Tors isTorsionPoint_iff_pow_eq_one)

section Abstract

variable {P S : Type*} [CommGroup P] [Group S]

theorem finite_tors_and_natCard_tors_le_mul (ι : S →* P) (hι : Function.Injective ι)
    (C : Set P) (hC : C.Finite) (hcov : ∀ x : P, ∃ c ∈ C, ∃ a : S, x = c * ι a) (m : ℕ)
    [Finite (Tors S m)] :
    Finite (Tors P m) ∧ Nat.card (Tors P m) ≤ Nat.card C * Nat.card (Tors S m) := by
  classical
  have hrep : ∀ c : C, ∃ r : P, (∃ x : Tors P m, ∃ a : S, (x : P) = c * ι a) →
      (r ^ m = 1 ∧ ∃ a : S, r = c * ι a) := by
    intro c
    by_cases h : ∃ x : Tors P m, ∃ a : S, (x : P) = c * ι a
    · obtain ⟨x, a, hx⟩ := h
      exact ⟨x, fun _ => ⟨x.2, a, hx⟩⟩
    · exact ⟨1, fun h' => (h h').elim⟩
  choose rep hrep using hrep
  have hcov' : ∀ x : Tors P m, ∃ c : C, ∃ a : S, (x : P) = c * ι a := by
    intro x
    obtain ⟨c, hc, a, ha⟩ := hcov x
    exact ⟨⟨c, hc⟩, a, ha⟩
  choose cst acst hcst using hcov'
  have hdiff : ∀ x : Tors P m, ∃ s : Tors S m, (x : P) = rep (cst x) * ι s := by
    intro x
    obtain ⟨hrm, a, ha⟩ := hrep (cst x) ⟨x, acst x, hcst x⟩
    refine ⟨⟨(a)⁻¹ * acst x, ?_⟩, ?_⟩
    · apply hι
      rw [map_pow, map_one]
      have hx : (x : P) ^ m = 1 := x.2
      have h1 : ι (a⁻¹ * acst x) = (rep (cst x))⁻¹ * (x : P) := by
        rw [map_mul, map_inv, ha, hcst x, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
      rw [h1, mul_pow, inv_pow, hx, hrm, inv_one, one_mul]
    · change (x : P) = rep (cst x) * ι (a⁻¹ * acst x)
      rw [map_mul, map_inv, ha, hcst x, mul_assoc, mul_inv_cancel_left]
  choose sof hsof using hdiff
  let φ : Tors P m → C × Tors S m := fun x => (cst x, sof x)
  have hφ : Function.Injective φ := by
    intro x y hxy
    simp only [φ, Prod.mk.injEq] at hxy
    apply Subtype.ext
    rw [hsof x, hsof y, hxy.1, hxy.2]
  have : Finite C := hC.to_subtype
  refine ⟨Finite.of_injective φ hφ, ?_⟩
  calc Nat.card (Tors P m) ≤ Nat.card (C × Tors S m) := Nat.card_le_card_of_injective φ hφ
    _ = Nat.card C * Nat.card (Tors S m) := Nat.card_prod _ _

end Abstract

open AbelianVarieties.NOSProofs.TorsionSpecializationInjection.TorsionInjection
  (torsionEquivOfEq torsionEquivBaseChange)

theorem isProper_of_smoothOfRelativeDimension_zero {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 0 f] [QuasiCompact f] :
    IsProper f := by
  have : IsFinite f := IsFinite.of_smoothOfRelativeDimension_zero_of_field f
  infer_instance

theorem isProper_of_isProper_pullback_snd {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsSeparated f] [LocallyOfFiniteType f]
    [IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))] : IsProper f := by
  set t := Spec.map (CommRingCat.ofHom (algebraMap k k')) with ht
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) t :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have : UniversallyClosed f :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      (IsPullback.of_hasPullback f t).flip hQ inferInstance
  exact IsProper.mk

end ComponentCount

end AbelianVarieties.NOSProofs.TorsionBounds

namespace GoodReductionJacobian.RelativeGroupLaw

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian

universe u

open AbelianVarieties.NOSProofs.TorsionBounds.ComponentCount
open AbelianVarieties.NOSProofs.ConnectedTorsionBounds.TorsionProperReduction
  (Tors isTorsionPoint_iff_pow_eq_one)
open AbelianVarieties.NOSProofs.TorsionSpecializationInjection.TorsionInjection
  (torsionEquivOfEq torsionEquivBaseChange)

theorem
    forall_isProper_or_exists_natCard_isTorsionPoint_le_mul_pow
    (k : Type u) [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (k' : Type u) [Field k'] [IsAlgClosed k'] [Algebra k k'] :
    (∀ (G₀ : Scheme.{u}) (i : G₀ ⟶ G) [IsOpenImmersion i],
        Set.range i =
          connectedComponent ((L.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint k)) →
        IsProper (i ≫ f)) ∨
    (0 < d ∧ ∃ c : ℕ, ∀ m : ℕ, (m : k) ≠ 0 →
        Finite {x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k'))) f //
            L.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap k k'))) m x} ∧
        Nat.card {x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k'))) f //
            L.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap k k'))) m x} ≤
          c * m ^ (2 * d - 1)) := by
  classical
  set t' : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k k')) with ht'
  set f' := pullback.snd f t' with hf'
  set L' := L.baseChange t' with hL'
  have hc' : L'.IsCommutative := RelativeGroupLaw.IsCommutative.baseChange t' hc
  have hbc : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (g : X ⟶ Y) => SmoothOfRelativeDimension d g) :=
    smoothOfRelativeDimension_isStableUnderBaseChange d
  have : SmoothOfRelativeDimension d f' :=
    hbc.of_isPullback (IsPullback.of_hasPullback f t')
      (inferInstanceAs (SmoothOfRelativeDimension d f))
  obtain ⟨G₀', i', L₀', hopen', hclosed', hirr', hrange', hhom', hcomm', S, hSfin, hcoset⟩ :=
    exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex
      k' L'
  have hc₀ : L₀'.IsCommutative := hcomm' hc'
  have : SmoothOfRelativeDimension d (i' ≫ f') := by
    have h : SmoothOfRelativeDimension (0 + d) (i' ≫ f') := inferInstance
    rwa [Nat.zero_add] at h
  have hpre : ∀ (G₀ : Scheme.{u}) (i : G₀ ⟶ G) [IsOpenImmersion i],
      Set.range i =
        connectedComponent ((L.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint k)) →
      Set.range (pullback.map (i ≫ f) t' f t' i (𝟙 _) (𝟙 _) (Category.comp_id _)
        ((Category.comp_id _).trans (Category.id_comp _).symm)) = Set.range i' := by
    intro G₀ i _ hrange
    obtain ⟨G₁, i₁, L₁, hopen₁, -, -, -, -, hrange₁, hbc₁, -⟩ :=
      exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent
        k L
    rw [Scheme.Pullback.range_map, hrange, ← hrange₁, hbc₁ k' t', hrange']
    have hid : Set.range (𝟙 (Spec (CommRingCat.of k'))) = Set.univ :=
      Set.range_eq_univ.mpr fun x => ⟨x, rfl⟩
    simp only [hid, Set.preimage_univ, Set.inter_univ, hL']
  by_cases hP : IsProper (i' ≫ f')
  · left
    intro G₀ i _ hrange
    let j := pullback.map (i ≫ f) t' f t' i (𝟙 _) (𝟙 _) (Category.comp_id _)
        ((Category.comp_id _).trans (Category.id_comp _).symm)
    have hj : j ≫ f' = pullback.snd (i ≫ f) t' := by
      simp only [j, hf', pullback.map, pullback.lift_snd, Category.comp_id]
    let e := IsOpenImmersion.isoOfRangeEq j i' (hpre G₀ i hrange)
    have he : e.hom ≫ (i' ≫ f') = pullback.snd (i ≫ f) t' := by
      rw [← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac, hj]
    have : IsProper (pullback.snd (i ≫ f) t') := by rw [← he]; infer_instance
    exact isProper_of_isProper_pullback_snd (k' := k') (i ≫ f)
  · right
    have hdpos : 0 < d := by
      by_contra hd
      have hd0 : d = 0 := by omega
      subst hd0
      exact hP (isProper_of_smoothOfRelativeDimension_zero (i' ≫ f'))
    have hK2 :=
      (GoodReductionJacobian.RelativeGroupLaw.isProper_or_natCard_isTorsionPoint_le_pow_sub_one
      k' (i' ≫ f') L₀' hc₀ d).resolve_left hP
    refine ⟨hdpos, Nat.card S, fun m hmk => ?_⟩
    have hmk' : (m : k') ≠ 0 := by
      intro h
      apply hmk
      have : algebraMap k k' (m : k) = 0 := by rwa [map_natCast]
      exact (map_eq_zero _).mp this
    obtain ⟨hfin₀, hcard₀⟩ := hK2 m hmk'
    let instP : CommGroup (SchemeHomOver (𝟙 (Spec (CommRingCat.of k'))) f') :=
      L'.pointCommGroup hc' (𝟙 (Spec (CommRingCat.of k')))
    let instS : Group (SchemeHomOver (𝟙 (Spec (CommRingCat.of k'))) (i' ≫ f')) :=
      L₀'.pointGroup (𝟙 (Spec (CommRingCat.of k')))
    let iPt : SchemeHomOver (i' ≫ f') f' := ⟨i', rfl⟩
    let ιS : SchemeHomOver (𝟙 (Spec (CommRingCat.of k'))) (i' ≫ f') →*
        SchemeHomOver (𝟙 (Spec (CommRingCat.of k'))) f' :=
      MonoidHom.mk' (fun y => NeronModelInfra.schemeHomOverComp y iPt)
        (fun x y => hhom' (𝟙 (Spec (CommRingCat.of k'))) x y)
    have hιinj : Function.Injective ιS := by
      intro y y' hyy'
      have hval : y.1 ≫ i' = y'.1 ≫ i' := congrArg Subtype.val hyy'
      exact Subtype.ext ((cancel_mono i').1 hval)
    have hcov : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k'))) f',
        ∃ c ∈ S, ∃ a, x = c * ιS a := by
      intro x
      obtain ⟨s, hs, a, ha⟩ := hcoset x
      exact ⟨s, hs, a, ha⟩
    have eS : {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k'))) (i' ≫ f') //
          L₀'.IsTorsionPoint (𝟙 (Spec (CommRingCat.of k'))) m x} ≃
        Tors (SchemeHomOver (𝟙 (Spec (CommRingCat.of k'))) (i' ≫ f')) m :=
      Equiv.subtypeEquivRight (fun x => isTorsionPoint_iff_pow_eq_one L₀' _ m x)
    have eP : {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k'))) f' //
          L'.IsTorsionPoint (𝟙 (Spec (CommRingCat.of k'))) m x} ≃
        Tors (SchemeHomOver (𝟙 (Spec (CommRingCat.of k'))) f') m :=
      Equiv.subtypeEquivRight (fun x => isTorsionPoint_iff_pow_eq_one L' _ m x)
    have : Finite (Tors (SchemeHomOver (𝟙 (Spec (CommRingCat.of k'))) (i' ≫ f')) m) :=
      Finite.of_equiv _ eS
    obtain ⟨hfinP, hle⟩ := finite_tors_and_natCard_tors_le_mul ιS hιinj S hSfin hcov m
    have hid : 𝟙 (Spec (CommRingCat.of k')) ≫ t' = Spec.map (CommRingCat.ofHom (algebraMap k k')) :=
      Category.id_comp _
    let e := ((torsionEquivBaseChange t' L (𝟙 _) m).trans (torsionEquivOfEq L hid m)).symm.trans eP
    refine ⟨Finite.of_equiv _ e.symm, ?_⟩
    rw [Nat.card_congr e]
    calc _ ≤ Nat.card S * Nat.card (Tors (SchemeHomOver (𝟙 (Spec (CommRingCat.of k'))) (i' ≫ f'))
      m) := hle
      _ ≤ Nat.card S * m ^ (2 * d - 1) := by
          apply Nat.mul_le_mul_left
          rw [← Nat.card_congr eS]
          exact hcard₀

end GoodReductionJacobian.RelativeGroupLaw
end
