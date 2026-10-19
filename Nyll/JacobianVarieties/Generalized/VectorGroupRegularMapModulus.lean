/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.GroupSchemes.VectorGroup
import Nyll.SchemeTheory.Affine.WeilRestriction.ScalarQuotientSchemePresheaf
import Nyll.AlgebraicCurves.Models.Charts.OpenPointValues
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Models.Charts.FiniteComplIsOpen
import Nyll.AlgebraicCurves.Models.Points.FieldEquivSymmMemEvalAtPointPlaceEqStalkClosedPointTo
import Nyll.AlgebraicCurves.Models.Divisors.CartierIdealEquiv
import Nyll.AlgebraicCurves.Models.FunctionFields.CurveRingEquivFunctionField
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.EssFiniteTypeFunctionField
import Nyll.AlgebraicCurves.Divisors.Modulus.SplitAffineModulus
import Nyll.AlgebraicCurves.Divisors.Modulus.ModulusFunctoriality
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.IEqProper
import Nyll.JacobianVarieties.Generalized.ModulusCurveIdeal
import Nyll.JacobianVarieties.Generalized.ModulusMapCondition
import Mathlib.Algebra.Group.Equiv.TypeTags

/-! # Effective moduli for actual maps to vector groups

The coordinates of a scheme morphism are global sections on its source.
Their images in the specified curve function field have the original
scheme point values. A common additive modulus, enlarged by the finite
boundary, therefore controls the actual vector-group-valued map. The
resulting effective Cartier ideal is the product of the corresponding
closed-point ideals, with its full multiplicities retained.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.GroupSchemes
open AlgebraicGeometry.GeneralizedJacobian CategoryTheory.Limits
open SchemeTheory.Affine.ScalarQuotientSchemePresheaf
open scoped CategoryTheory.MonObj

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)

/-- The actual point group of the vector group, in additive scalar coordinates. -/
def vectorPointCoordinates (n : ℕ) :
    Additive (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (vectorGroup K n).X) ≃+
      (Fin n → K) :=
  ((vectorGroupPointEquiv K n (Over.mk (𝟙 _))).toAdditive.trans
    (AddEquiv.additiveMultiplicative _)).trans
      (AddEquiv.piCongrRight fun _ =>
        (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toAddEquiv)

/-- Global sections on a nonempty open, mapped to the specified function field
through their germs on the original curve. -/
def openSectionFunction (U : M.C.Opens) [Nonempty U] : Γ(U, ⊤) →+* F :=
  let V := U.ι ''ᵁ ⊤
  let _ : Nonempty V :=
    ⟨⟨U.ι (Classical.choice inferInstance), ⟨Classical.choice inferInstance, trivial, rfl⟩⟩⟩
  M.ffEquiv.symm.toRingHom.comp (M.C.germToFunctionField V).hom

/-- The function-field image of a section retains its actual scheme point value. -/
theorem openSectionFunction_eval (U : M.C.Opens) [Nonempty U]
    (s : Γ(U, ⊤))
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (U.ι ≫ M.toBase)) :
    (M.openPointPlace U x).evalAt (M.openSectionFunction U s) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom (x.1.appTop s) := by
  let V := U.ι ''ᵁ ⊤
  let z : U := x.1.base (IsLocalRing.closedPoint K)
  have hz : (z : M.C) ∈ V := ⟨z, trivial, rfl⟩
  have : Nonempty V := ⟨⟨z, hz⟩⟩
  let p : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase :=
    ⟨x.1 ≫ U.ι, (Category.assoc _ _ _).trans x.2⟩
  let t := M.C.presheaf.germ V (z : M.C) hz s
  obtain ⟨_, _, heval⟩ :=
    M.ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo p t
  have ht : algebraMap (M.C.presheaf.stalk (z : M.C)) M.C.functionField t =
      M.C.germToFunctionField V s :=
    M.C.algebraMap_germ_eq_germToFunctionField hz s
  change (M.pointEquivPlace p).evalAt
    (M.ffEquiv.symm (M.C.germToFunctionField V s)) = _
  refine ((congrArg (fun a : M.C.functionField =>
    (M.pointEquivPlace p).evalAt (M.ffEquiv.symm a)) ht).symm.trans heval).trans ?_
  have hg : (U.stalkIso z).inv t = U.toScheme.presheaf.germ ⊤ z trivial s :=
    ConcreteCategory.congr_hom (U.germ_stalkIso_inv ⊤ z trivial) s
  calc
    (Scheme.stalkClosedPointTo p.1).hom t =
        (Scheme.stalkClosedPointTo x.1).hom ((U.stalkIso z).inv t) := by
      rw [Scheme.stalkClosedPointTo_comp, Scheme.Opens.stalkIso_inv]
      rfl
    _ = (Scheme.stalkClosedPointTo x.1).hom
        (U.toScheme.presheaf.germ ⊤ z trivial s) := congrArg _ hg
    _ = (Scheme.ΓSpecIso (CommRingCat.of K)).hom (x.1.appTop s) := by
      exact ConcreteCategory.congr_hom
        (Scheme.germ_stalkClosedPointTo x.1 ⊤ trivial) s

/-- Rational coordinate functions extracted from the actual vector-group morphism. -/
def vectorMapRationalCoordinates (U : M.C.Opens) [Nonempty U] (n : ℕ)
    (q : SchemeHomOver (U.ι ≫ M.toBase) (vectorGroup K n).X.hom) : Fin n → F :=
  fun i => M.openSectionFunction U
    ((vectorGroupPointEquiv K n (Over.mk (U.ι ≫ M.toBase))
      (commGroupPointEquiv (vectorGroup K n) (U.ι ≫ M.toBase) q)).toAdd i)

/-- Evaluating the extracted functions gives the original scheme morphism's
coordinates at every point of its open domain. -/
theorem vectorMapRationalCoordinates_eval (U : M.C.Opens) [Nonempty U] (n : ℕ)
    (q : SchemeHomOver (U.ι ≫ M.toBase) (vectorGroup K n).X.hom)
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (U.ι ≫ M.toBase)) (i : Fin n) :
    (M.openPointPlace U x).evalAt (M.vectorMapRationalCoordinates U n q i) =
      vectorPointCoordinates (K := K) n
        (commGroupPointValue (vectorGroup K n) (𝟙 _)
          (NeronModelInfra.schemeHomOverComp x q)) i := by
  let s := (vectorGroupPointEquiv K n (Over.mk (U.ι ≫ M.toBase))
    (commGroupPointEquiv (vectorGroup K n) (U.ι ≫ M.toBase) q)).toAdd i
  have heval := M.openSectionFunction_eval U s x
  change (M.openPointPlace U x).evalAt (M.openSectionFunction U s) = _
  rw [heval]
  change _ = (Scheme.ΓSpecIso (CommRingCat.of K)).hom
    ((vectorGroupPointEquiv K n (Over.mk (𝟙 _))
      ((Over.homMk x.1 x.2 : Over.mk (𝟙 _) ⟶ Over.mk (U.ι ≫ M.toBase)) ≫
        commGroupPointEquiv (vectorGroup K n) (U.ι ≫ M.toBase) q)).toAdd i)
  rw [vectorGroupPointEquiv_naturality]
  rfl

private theorem exists_openPointPlace_of_mem (U : M.C.Opens) (w : Place K F)
    (hw : (M.placeEquiv.symm w).1 ∈ U) :
    ∃ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (U.ι ≫ M.toBase),
      M.openPointPlace U x = w := by
  let p := M.pointEquivPlace.symm w
  have hp : pointEquivClosedPoint M.toBase p = M.placeEquiv.symm w := by
    apply M.placeEquiv.injective
    exact (M.pointEquivPlace.apply_symm_apply w).trans
      (M.placeEquiv.apply_symm_apply w).symm
  have hmem : p.1.base (IsLocalRing.closedPoint K) ∈ U := by
    rw [← hp] at hw
    exact hw
  have hrange : Set.range p.1 ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hz : z = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    rw [hz]
    exact hmem
  let x := IsOpenImmersion.lift U.ι p.1 hrange
  have hx : x ≫ U.ι = p.1 := IsOpenImmersion.lift_fac _ _ _
  have hxc : x ≫ (U.ι ≫ M.toBase) = 𝟙 _ := by
    rw [← Category.assoc, hx]
    exact p.2
  refine ⟨⟨x, hxc⟩, ?_⟩
  change M.pointEquivPlace _ = w
  rw [← M.pointEquivPlace.apply_symm_apply w]
  apply congrArg M.pointEquivPlace
  exact Subtype.ext hx

/-- Finite boundary enlargement transports a proved coordinate modulus to
the actual point group of a regular map. -/
theorem exists_regularMap_modulus_of_point_coordinates (U : M.C.Opens)
    (hU : (U : Set M.C).Nonempty) (G : CommGrp (Over (Spec (CommRingCat.of K))))
    (q : SchemeHomOver (U.ι ≫ M.toBase) G.X.hom)
    {A : Type*} [AddCommGroup A]
    (e : Additive (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) ≃+ A)
    (a : Place K F → A) (E : Modulus K F) (hE : E.HasModulus a)
    (heval : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (U.ι ≫ M.toBase),
      a (M.openPointPlace U x) =
        e (commGroupPointValue G (𝟙 _) (NeronModelInfra.schemeHomOverComp x q))) :
    ∃ D : Modulus K F,
      (∀ w, D w = 0 → (M.placeEquiv.symm w).1 ∈ U) ∧
      D.HasModulus (M.regularMapValues U G q) := by
  classical
  have : IsCurveOver K F :=
    isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  have : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  let p : Place K F → M.C := fun w => (M.placeEquiv.symm w).1
  have hp : Function.Injective p := Subtype.val_injective.comp M.placeEquiv.symm.injective
  have hfin : (p ⁻¹' (U : Set M.C)ᶜ).Finite :=
    Set.Finite.preimage hp.injOn (finite_compl_of_isOpen M.toBase U hU)
  let B : Modulus K F := Finsupp.ofSupportFinite
    (fun w => if p w ∈ U then 0 else 1) (hfin.subset (by
      intro w hw hmem
      exact hw (ite_eq_left hmem)))
  have hboundary (w : Place K F) (hw : (E + B) w = 0) : p w ∈ U := by
    change E w + (if p w ∈ U then 0 else 1) = 0 at hw
    by_contra hn
    rw [ite_eq_right hn] at hw
    omega
  refine ⟨E + B, hboundary, ?_⟩
  have hmod := (hE.mono (show E ≤ E + B from le_add_of_nonneg_right zero_le)).map
    e.symm.toAddMonoidHom
  apply hmod.congr
  intro w hw
  obtain ⟨x, rfl⟩ := M.exists_openPointPlace_of_mem U w (hboundary w hw)
  apply e.injective
  simp only [AddEquiv.coe_toAddMonoidHom,
    AddEquiv.apply_symm_apply, M.regularMapValues_apply]
  exact heval x

/-- An actual map from a nonempty open curve to a vector group has a full
modulus containing the entire boundary of its original domain. -/
theorem exists_vectorGroup_regularMap_modulus (U : M.C.Opens)
    (hU : (U : Set M.C).Nonempty) (n : ℕ)
    (q : SchemeHomOver (U.ι ≫ M.toBase) (vectorGroup K n).X.hom) :
    ∃ D : Modulus K F,
      (∀ w, D w = 0 → (M.placeEquiv.symm w).1 ∈ U) ∧
      D.HasModulus (M.regularMapValues U (vectorGroup K n) q) := by
  have : Nonempty U := ⟨⟨hU.choose, hU.choose_spec⟩⟩
  have : IsCurveOver K F :=
    isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  have : Algebra.EssFiniteType K F := by
    let _ : Algebra K M.C.functionField := M.functionFieldAlgebra
    exact (Algebra.EssFiniteType.iff_of_algEquiv M.ffAlgEquiv).mpr
      (essFiniteType_functionField M.toBase)
  obtain ⟨E, hE⟩ := Modulus.exists_vector_modulus (K := K)
    (M.vectorMapRationalCoordinates U n q)
  refine M.exists_regularMap_modulus_of_point_coordinates U hU (vectorGroup K n) q
    (vectorPointCoordinates (K := K) n) _ E hE ?_
  intro x
  funext i
  exact M.vectorMapRationalCoordinates_eval U n q x i

/-- The closed-point ideal product of a modulus containing the finite
boundary has its entire open complement inside the original domain. -/
theorem pointIdealProduct_complement_le (U : M.C.Opens)
    (hU : (U : Set M.C).Nonempty) (D : Modulus K F)
    (hboundary : ∀ w, D w = 0 → (M.placeEquiv.symm w).1 ∈ U) :
    (M.pointIdealProduct D).support.compl ≤ U := by
  let I := M.pointIdealProduct D
  have hI : I.IsInvertible := M.pointIdealProduct_isInvertible D
  intro y hy
  by_contra hn
  have hη : genericPoint M.C ∈ U :=
    ((genericPoint_spec M.C).mem_open_set_iff U.isOpen).mpr
      ⟨hU.choose, trivial, hU.choose_spec⟩
  have hyη : y ≠ genericPoint M.C := by
    intro heq
    exact hn (heq.symm ▸ hη)
  let z : closedPoints M.C :=
    ⟨y, isClosed_singleton_of_ne_genericPoint M.toBase y hyη⟩
  have hz : M.cartierModulus I hI (M.placeEquiv z) = 0 :=
    (M.cartierModulus_eq_zero_iff I hI (M.placeEquiv z)).mpr (by
      rw [M.placeEquiv.symm_apply_apply]
      exact hy)
  rw [M.cartierModulus_pointIdealProduct] at hz
  have hmem := hboundary (M.placeEquiv z) hz
  rw [M.placeEquiv.symm_apply_apply] at hmem
  exact hn hmem

/-- The vector-group modulus is supplied by an actual effective Cartier
ideal, whose open complement lies in the original domain of the morphism. -/
theorem exists_vectorGroup_cartierModulus (U : M.C.Opens)
    (hU : (U : Set M.C).Nonempty) (n : ℕ)
    (q : SchemeHomOver (U.ι ≫ M.toBase) (vectorGroup K n).X.hom) :
    ∃ (I : M.C.IdealSheafData) (hI : I.IsInvertible),
      I.support.compl ≤ U ∧
      (M.cartierModulus I hI).HasModulus (M.regularMapValues U (vectorGroup K n) q) := by
  obtain ⟨D, hboundary, hD⟩ := M.exists_vectorGroup_regularMap_modulus U hU n q
  let I := M.pointIdealProduct D
  have hI : I.IsInvertible := M.pointIdealProduct_isInvertible D
  refine ⟨I, hI, M.pointIdealProduct_complement_le U hU D hboundary, ?_⟩
  simpa only [I, M.cartierModulus_pointIdealProduct] using hD

omit [IsAlgClosed K] in
/-- An actual invertible ideal on the proper curve is realized by a finite
flat relative divisor, with the original curve ideal unchanged. -/
theorem exists_relativeDivisor_ideal (I : M.C.IdealSheafData)
    (hI : I.IsInvertible) :
    ∃ (d : ℕ) (D : RelEffCartierDiv M.toBase d (𝟙 (Spec (CommRingCat.of K)))),
      modulusCurveIdeal D = I := by
  have hfin : ((I.comap (pullback.fst M.toBase (𝟙 (Spec (CommRingCat.of K))))).support :
      Set ↥(pullback M.toBase (𝟙 (Spec (CommRingCat.of K))))).Finite := by
    rw [Scheme.IdealSheafData.support_comap]
    change ((pullback.fst M.toBase (𝟙 (Spec (CommRingCat.of K)))) ⁻¹'
      (I.support : Set M.C)).Finite
    exact Set.Finite.preimage
      (pullback.fst M.toBase (𝟙 (Spec (CommRingCat.of K)))).isOpenEmbedding.injective.injOn
      (M.cartierSupport_finite I hI)
  obtain ⟨d, D, hD⟩ := RelEffCartierDiv.exists_I_eq_of_isProper_of_support_finite
    (𝟙 (Spec (CommRingCat.of K))) _ hfin
  refine ⟨d, D, ?_⟩
  rw [modulusCurveIdeal_eq_comap, hD, ← Scheme.IdealSheafData.comap_comp,
    IsIso.inv_hom_id, Scheme.IdealSheafData.comap_id]

/-- Restricting to the actual modulus complement preserves a principal-divisor
condition proved using the values of the original regular map. -/
theorem regularMapHasModulus_restriction_of_values (U : M.C.Opens)
    (G : CommGrp (Over (Spec (CommRingCat.of K))))
    (q : SchemeHomOver (U.ι ≫ M.toBase) G.X.hom)
    {d : ℕ} (D : RelEffCartierDiv M.toBase d (𝟙 (Spec (CommRingCat.of K))))
    (hVU : modulusComplement (modulusCurveMap D) ≤ U)
    (hmod : (M.cartierModulus (modulusCurveIdeal D)
      (modulusCurveIdeal_isInvertible D)).HasModulus (M.regularMapValues U G q)) :
    M.regularMapHasModulus D G
      ⟨M.C.homOfLE hVU ≫ q.1, by
        rw [Category.assoc, q.2, ← Category.assoc, Scheme.homOfLE_ι]⟩ := by
  let V := modulusComplement (modulusCurveMap D)
  let j : SchemeHomOver (V.ι ≫ M.toBase) (U.ι ≫ M.toBase) :=
    ⟨M.C.homOfLE hVU, by rw [← Category.assoc, Scheme.homOfLE_ι]⟩
  let qV : SchemeHomOver (V.ι ≫ M.toBase) G.X.hom :=
    NeronModelInfra.schemeHomOverComp j q
  change (M.cartierModulus (modulusCurveIdeal D)
    (modulusCurveIdeal_isInvertible D)).HasModulus (M.regularMapValues V G qV)
  refine hmod.congr (fun w hw => ?_)
  have hwV : (M.placeEquiv.symm w).1 ∈ V :=
    (M.cartierModulus_eq_zero_iff (modulusCurveIdeal D)
      (modulusCurveIdeal_isInvertible D) w).mp hw
  obtain ⟨x, rfl⟩ := M.exists_openPointPlace_of_mem V w hwV
  let y : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (U.ι ≫ M.toBase) :=
    NeronModelInfra.schemeHomOverComp x j
  have hy : M.openPointPlace U y = M.openPointPlace V x := by
    apply congrArg M.pointEquivPlace
    apply Subtype.ext
    exact (Category.assoc x.1 (M.C.homOfLE hVU) U.ι).trans
      (congrArg (fun r : V.toScheme ⟶ M.C => x.1 ≫ r)
        (Scheme.homOfLE_ι M.C hVU))
  have hcomp : NeronModelInfra.schemeHomOverComp y q =
      NeronModelInfra.schemeHomOverComp x qV :=
    NeronModelInfra.schemeHomOverComp_assoc x j q
  calc
    M.regularMapValues U G q (M.openPointPlace V x) =
        M.regularMapValues U G q (M.openPointPlace U y) :=
      congrArg (M.regularMapValues U G q) hy.symm
    _ = commGroupPointValue G (𝟙 _) (NeronModelInfra.schemeHomOverComp y q) :=
      M.regularMapValues_apply U G q y
    _ = commGroupPointValue G (𝟙 _) (NeronModelInfra.schemeHomOverComp x qV) :=
      congrArg (commGroupPointValue G (𝟙 (Spec (CommRingCat.of K)))) hcomp
    _ = M.regularMapValues V G qV (M.openPointPlace V x) :=
      (M.regularMapValues_apply V G qV x).symm

/-- A vector-group morphism has an actual relative effective Cartier modulus.
The morphism on its complement is the restriction of the original map. -/
theorem exists_vectorGroup_regularMapHasModulus (U : M.C.Opens)
    (hU : (U : Set M.C).Nonempty) (n : ℕ)
    (q : SchemeHomOver (U.ι ≫ M.toBase) (vectorGroup K n).X.hom) :
    ∃ (d : ℕ) (D : RelEffCartierDiv M.toBase d (𝟙 (Spec (CommRingCat.of K))))
      (hDU : modulusComplement (modulusCurveMap D) ≤ U),
      M.regularMapHasModulus D (vectorGroup K n)
        ⟨M.C.homOfLE hDU ≫ q.1, by
          rw [Category.assoc, q.2, ← Category.assoc, Scheme.homOfLE_ι]⟩ := by
  obtain ⟨I, hI, hIU, hmod⟩ := M.exists_vectorGroup_cartierModulus U hU n q
  obtain ⟨d, D, hDI⟩ := M.exists_relativeDivisor_ideal I hI
  have hVU : modulusComplement (modulusCurveMap D) ≤ U := by
    change (modulusCurveIdeal D).support.compl ≤ U
    rw [hDI]
    exact hIU
  refine ⟨d, D, hVU, ?_⟩
  apply M.regularMapHasModulus_restriction_of_values U (vectorGroup K n) q D hVU
  simpa only [hDI] using hmod

end AlgebraicCurve.CurveModel
