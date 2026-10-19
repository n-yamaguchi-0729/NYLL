/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.FiniteCurveTraceTameIntegralDifference
import Nyll.JacobianVarieties.Generalized.RationalFunctionTraceNativeData
import Nyll.JacobianVarieties.Generalized.RationalFunctionTraceFinitePoints
import Nyll.JacobianVarieties.Generalized.RationalFunctionTraceAffineConstancy
import Nyll.JacobianVarieties.Generalized.RationalFunctionTraceAffineFormalDifference
import Nyll.JacobianVarieties.Generalized.WholeCurveGroupModulus
import Nyll.JacobianVarieties.Generalized.VectorGroupRegularMapModulus
import Nyll.AlgebraicCurves.Divisors.Modulus.TameReciprocalModulusReduction
import Nyll.AlgebraicCurves.Places.Orders.TameReciprocalInfinity
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.EssFiniteTypeFunctionField
import Nyll.SchemeTheory.LocalGeometry.SmoothStalks

/-! # A full modulus for an actual map to a commutative group

Over an algebraically closed field, the finite boundary and the actual
formal group-difference bound determine one tame contact order. Every
test function of that exact order defines an actual finite separable
reciprocal trace on the affine line. The integral difference of that trace
forces it to be constant, and its finite fibres annihilate the full
principal evaluation. Exact-contact factorization then proves the modulus
condition for all test functions, including inseparable ones.

The base point and the formal coordinate bounds are chosen before the test
function. The curve, its function field, the finite map, and its full
Cartier fibres are retained throughout.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve TopologicalSpace
open NeronModelInfra GoodReductionJacobian
open scoped BigOperators CategoryTheory.MonObj AlgebraicCurve.Place

namespace AlgebraicGeometry.GeneralizedJacobian

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

private theorem zero_hasModulus_top_values
    {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (M : CurveModel K F)
    (G : CommGrp (Over (Spec (.of K)))) [IsSeparated G.X.hom]
    (q : SchemeHomOver ((⊤ : M.C.Opens).ι ≫ M.toBase) G.X.hom) :
    (0 : Modulus K F).HasModulus (M.regularMapValues ⊤ G q) := by
  let qC : Over.mk M.toBase ⟶ G.X :=
    Over.homMk (M.C.topIso.inv ≫ q.1) (by
      change (M.C.topIso.inv ≫ q.1) ≫ G.X.hom = M.toBase
      calc
        _ = M.C.topIso.inv ≫ (q.1 ≫ G.X.hom) := Category.assoc _ _ _
        _ = M.C.topIso.inv ≫ ((⊤ : M.C.Opens).ι ≫ M.toBase) :=
          congrArg (fun f => M.C.topIso.inv ≫ f) q.2
        _ = (M.C.topIso.inv ≫ (⊤ : M.C.Opens).ι) ≫ M.toBase :=
          (Category.assoc _ _ _).symm
        _ = (𝟙 M.C) ≫ M.toBase :=
          congrArg (fun f : M.C ⟶ M.C => f ≫ M.toBase) M.C.topIso.inv_hom_id
        _ = M.toBase := Category.id_comp _)
  apply (M.zero_hasModulus_of_separated_group G qC).congr
  intro w _
  let p := M.pointEquivPlace.symm w
  let x : SchemeHomOver (𝟙 (Spec (.of K))) ((⊤ : M.C.Opens).ι ≫ M.toBase) :=
    ⟨p.1 ≫ M.C.topIso.inv, by
      calc
        _ = p.1 ≫ (M.C.topIso.inv ≫ (⊤ : M.C.Opens).ι) ≫ M.toBase := by
          simp only [Category.assoc]
        _ = p.1 ≫ (𝟙 M.C) ≫ M.toBase :=
          congrArg (fun f : M.C ⟶ M.C => p.1 ≫ f ≫ M.toBase)
            M.C.topIso.inv_hom_id
        _ = 𝟙 _ := by rw [Category.id_comp]; exact p.2⟩
  have hx : M.openPointPlace ⊤ x = w := by
    change M.pointEquivPlace
      ⟨x.1 ≫ (⊤ : M.C.Opens).ι, (Category.assoc _ _ _).trans x.2⟩ = w
    have hp : (⟨x.1 ≫ (⊤ : M.C.Opens).ι,
        (Category.assoc _ _ _).trans x.2⟩ :
        SchemeHomOver (𝟙 (Spec (.of K))) M.toBase) = p := by
      apply Subtype.ext
      change (p.1 ≫ M.C.topIso.inv) ≫ (⊤ : M.C.Opens).ι = p.1
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun f : M.C ⟶ M.C => p.1 ≫ f) M.C.topIso.inv_hom_id).trans
          (Category.comp_id p.1))
    rw [hp, M.pointEquivPlace.apply_symm_apply]
  have hv := M.regularMapValues_apply ⊤ G q x
  rw [hx] at hv
  refine (hv.trans ?_).symm
  change Additive.ofMul _ = Additive.ofMul _
  apply congrArg Additive.ofMul
  apply Over.OverMorphism.ext
  exact Category.assoc p.1 M.C.topIso.inv q.1

/-- An actual regular map from a nonempty open smooth proper curve to any
separated commutative group locally of finite type has a full modulus
containing its original boundary. The native curve function field supplies
the divisor evaluator; no reciprocity or trace-constancy premise is added. -/
theorem exists_group_regularMap_modulus
    {K : Type u} [Field K] [IsAlgClosed K]
    {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (.of K)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    (U : C.Opens) (hU : (U : Set C).Nonempty)
    (G : CommGrp (Over (Spec (.of K)))) [IsSeparated G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (q : SchemeHomOver (U.ι ≫ c) G.X.hom) :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    let M := CurveModel.ofSmoothProperCurve c
    ∃ D : Modulus K C.functionField,
      (∀ w, D w = 0 ↔ (M.placeEquiv.symm w).1 ∈ U) ∧
      D.HasModulus (M.regularMapValues U G q) := by
  intro algC M
  classical
  by_cases htop : U = ⊤
  · subst U
    exact ⟨0, fun _ => iff_of_true rfl trivial, zero_hasModulus_top_values M G q⟩
  have : GeometricallyIntegral c := geometricallyIntegral_of_isAlgClosed c
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral C := IsNormalIntegral.of_stalks C
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk c x).2)
  have : IsCurveOver K C.functionField :=
    isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      c (RingEquiv.refl _) (fun _ => rfl)
  have : Algebra.EssFiniteType K C.functionField := essFiniteType_functionField c
  have : Nonempty U := ⟨⟨hU.choose, hU.choose_spec⟩⟩
  have : JacobsonSpace U := LocallyOfFiniteType.jacobsonSpace (U.ι ≫ c)
  obtain ⟨xε, _, hxε⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty : (Set.univ : Set U).Nonempty) isClosed_univ.isLocallyClosed
  let ε : SchemeHomOver (𝟙 (Spec (.of K))) (U.ι ≫ c) :=
    ⟨pointOfClosedPoint (U.ι ≫ c) xε hxε,
      pointOfClosedPoint_comp (U.ι ≫ c) xε hxε⟩
  let onePoint := (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G.X).left
    (IsLocalRing.closedPoint K)
  obtain ⟨_, ⟨V, hV, rfl⟩, hmem, _⟩ :=
    G.X.left.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ onePoint) isOpen_univ
  have hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G.X).left ⊆ V := by
    rintro _ ⟨y, rfl⟩
    let yK : Spec (.of K) := y
    have hy : yK = (IsLocalRing.closedPoint K : Spec (.of K)) := Subsingleton.elim _ _
    change (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G.X).left yK ∈ V
    rw [hy]
    exact hmem
  obtain ⟨t, _ht, Dpole, htrace⟩ :=
    exists_finiteCurveTrace_uniform_tame_integral_difference c U hU ε G q V hV hunit
  let centre : Place K C.functionField → C := fun w => (M.placeEquiv.symm w).1
  have hcentre : Function.Injective centre :=
    fun v w h => M.placeEquiv.symm.injective (Subtype.ext h)
  have hfinite : (centre ⁻¹' (U : Set C)ᶜ).Finite :=
    Set.Finite.preimage hcentre.injOn (finite_compl_of_isOpen c U hU)
  let S := hfinite.toFinset
  have hS (w : Place K C.functionField) : w ∈ S ↔ (M.placeEquiv.symm w).1 ∉ U :=
    hfinite.mem_toFinset
  have hSnonempty : S.Nonempty := by
    by_contra hSempty
    have hall : ∀ y : C, y ∈ U := by
      intro y
      by_contra hy
      have hη : genericPoint C ∈ U :=
        ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr
          ⟨hU.choose, trivial, hU.choose_spec⟩
      let y₀ : closedPoints C :=
        ⟨y, isClosed_singleton_of_ne_genericPoint c y (fun h => hy (h.symm ▸ hη))⟩
      have hcentreY : (show C from (M.placeEquiv.symm (M.placeEquiv y₀)).1) = y :=
        congrArg (fun z : closedPoints M.C => (show C from z.1))
          (M.placeEquiv.symm_apply_apply (show closedPoints M.C from y₀))
      have hw : M.placeEquiv y₀ ∈ S :=
        (hS _).mpr (fun hmem => hy (hcentreY ▸ hmem))
      exact hSempty ⟨_, hw⟩
    exact htop (top_unique (fun y _ => hall y))
  let cost : Place K C.functionField → ℤ := fun w =>
    max 1 (2 * (Dpole w : ℤ)) - min (w.ord t) (max 1 (2 * (Dpole w : ℤ)))
  obtain ⟨e, hepos, heK, hecost⟩ :=
    Place.exists_common_tame_order S (fun w => (cost w).toNat)
  have hlarge (w : Place K C.functionField) (hw : (M.placeEquiv.symm w).1 ∉ U) :
      cost w < (e : ℤ) := by
    have hew := hecost w ((hS w).mpr hw)
    have hcw := Int.self_le_toNat (cost w)
    exact lt_of_le_of_lt hcw (by exact_mod_cast hew)
  let D : Modulus K C.functionField :=
    Finsupp.onFinset S (fun w => if w ∈ S then e + 1 else 0)
      (by intro w hw; by_contra hn; exact hw (ite_eq_right hn))
  have hD (w : Place K C.functionField) : D w = if w ∈ S then e + 1 else 0 := rfl
  have hDsupport (w : Place K C.functionField) : w ∈ D.support ↔ w ∈ S := by
    rw [Finsupp.mem_support_iff, hD]
    by_cases hw : w ∈ S
    · rw [ite_eq_left hw]
      exact iff_of_true (Nat.succ_ne_zero e) hw
    · rw [ite_eq_right hw]
      exact iff_of_false (not_ne_iff.mpr rfl) hw
  refine ⟨D, ?_, ?_⟩
  · intro w
    constructor
    · intro hw
      by_contra hnot
      have hws := (hS w).mpr hnot
      rw [hD, ite_eq_left hws] at hw
      exact Nat.succ_ne_zero e hw
    · intro hw
      rw [hD, ite_eq_right (fun hs => ((hS w).mp hs) hw)]
  obtain ⟨w₀, hw₀⟩ := hSnonempty
  apply Modulus.hasModulus_of_finiteSeparable_reciprocal_tests D
    ⟨w₀, (hDsupport w₀).mpr hw₀⟩ (M.regularMapValues U G q) (fun _ => e)
    (fun _ _ => hepos)
    (fun w hw => by rw [hD, ite_eq_left ((hDsupport w).mp hw)]; omega)
    (fun _ _ => heK)
  intro g hg htr hfiniteg hsepg
  have : FiniteDimensional (IntermediateField.adjoin K {((g : C.functionField) - 1)⁻¹})
      C.functionField := hfiniteg
  have : Algebra.IsSeparable
      (IntermediateField.adjoin K {((g : C.functionField) - 1)⁻¹}) C.functionField := hsepg
  have hcontact (w : Place K C.functionField)
      (hw : (M.placeEquiv.symm w).1 ∉ U) : w.ord ((g : C.functionField) - 1) = (e : ℤ) :=
    hg w ((hDsupport w).mpr ((hS w).mpr hw))
  have hw₀boundary := (hS w₀).mp hw₀
  have hg₀ : (g : C.functionField) ≠ 1 := by
    intro hg₀
    have hh := hcontact w₀ hw₀boundary
    rw [hg₀, sub_self, Place.ord_zero] at hh
    omega
  have hz : ((g : C.functionField) - 1)⁻¹ ∉ Set.range (algebraMap K C.functionField) := by
    rintro ⟨a, ha⟩
    apply htr
    rw [← ha]
    exact isAlgebraic_algebraMap a
  have hpolar (y : closedPoints C) (hy : y.1 ∉ U) :
      (M.placeOfPoint y).ord (((g : C.functionField) - 1)⁻¹) < 0 := by
    let yM : closedPoints M.C := y
    have hcentreY : (show C from (M.placeEquiv.symm (M.placeEquiv yM)).1) = y.1 :=
      congrArg (fun z : closedPoints M.C => (show C from z.1))
        (M.placeEquiv.symm_apply_apply yM)
    have hh := hcontact (M.placeEquiv yM) (fun hmem => hy (hcentreY ▸ hmem))
    have hnegative : -(M.placeEquiv yM).ord ((g : C.functionField) - 1) < 0 := by
      rw [hh]
      omega
    exact ((M.placeOfPoint yM).ord_inv ((g : C.functionField) - 1)).trans_lt hnegative
  let P := ProjSpace.projectiveLineRatFuncModel K
  obtain ⟨φ, hφX, hφ, hfiniteφ, π, hπ, hfinπ, hflatπ, hlfpπ, hn, hgeneric,
      _hchart, _εg, l, hl, _τg, _hτg⟩ :=
    exists_rationalFunctionTrace_affineLine M (((g : C.functionField) - 1)⁻¹)
      hz U hU hpolar G q
  change C ⟶ P.C at π
  change π ≫ P.toBase = c at hπ
  change IsFinite π at hfinπ
  change Flat π at hflatπ
  change LocallyOfFinitePresentation π at hlfpπ
  have : IsFinite π := hfinπ
  have : Flat π := hflatπ
  have : LocallyOfFinitePresentation π := hlfpπ
  have htrφ : Transcendental K (φ RatFunc.X) := by
    rw [hφX]
    exact htr
  have : FiniteDimensional (IntermediateField.adjoin K {φ RatFunc.X}) C.functionField := by
    rw [hφX]
    exact hfiniteg
  have : Algebra.IsSeparable (IntermediateField.adjoin K {φ RatFunc.X}) C.functionField := by
    rw [hφX]
    exact hsepg
  let algB : Algebra K P.C.functionField := P.functionFieldAlgebra
  let ψ : P.C.functionField →ₐ[K] C.functionField :=
    φ.comp P.ffAlgEquiv.symm.toAlgHom
  let algBF : Algebra P.C.functionField C.functionField := ψ.toRingHom.toAlgebra
  obtain ⟨htower, hfiniteBF, hsepBF, p, hpX, hparameter⟩ :=
    reciprocalTrace_native_field_data P M φ htrφ g hφX
  have : IsScalarTower K P.C.functionField C.functionField := by
    change IsScalarTower K P.C.functionField C.functionField at htower
    exact htower
  have : FiniteDimensional P.C.functionField C.functionField := by
    change FiniteDimensional P.C.functionField C.functionField at hfiniteBF
    exact hfiniteBF
  have : Algebra.IsSeparable P.C.functionField C.functionField := by
    change Algebra.IsSeparable P.C.functionField C.functionField at hsepBF
    exact hsepBF
  have hparameterNative : algebraMap P.C.functionField C.functionField (p RatFunc.X) =
      (g : C.functionField) - 1 := by
    change algebraMap P.C.functionField C.functionField (p RatFunc.X) =
      (g : C.functionField) - 1 at hparameter
    exact hparameter
  have : IsCurveOver K P.C.functionField :=
    isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      P.toBase (RingEquiv.refl _) (fun _ => rfl)
  have : GeometricallyIntegral P.toBase := geometricallyIntegral_of_isAlgClosed P.toBase
  have hgenericNative : C.fromSpecStalk (genericPoint C) ≫ π =
      Spec.map (CommRingCat.ofHom (algebraMap P.C.functionField C.functionField)) ≫
        P.C.fromSpecStalk (genericPoint P.C) := by
    change C.fromSpecStalk (genericPoint C) ≫ π =
      Spec.map (CommRingCat.ofHom (algebraMap P.C.functionField C.functionField)) ≫
        P.C.fromSpecStalk (genericPoint P.C) at hgeneric
    exact hgeneric
  obtain ⟨hW, α, θ, _hαs, hαorder, _hθres, hθshift, pint, hpint, hred⟩ :=
    htrace P.C P.toBase π hπ (finrankAlong K φ) hn hgenericNative p g hparameterNative e
      hepos heK hcontact hlarge w₀ hw₀boundary
  let W := finiteMapTraceLocus c P.toBase π hπ (finrankAlong K φ) hn U
  let trace := finiteCurveTrace c P.toBase π hπ (finrankAlong K φ) hn U ε G q
  change Spec (.of (Polynomial K)) ⟶ W.toScheme at l
  change l ≫ W.ι = ProjSpace.projectiveLinePolynomialChart K at hl
  let τAffine : SchemeHomOver
      (Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K)))) G.X.hom :=
    ⟨l ≫ trace.1, by
      rw [Category.assoc, trace.2, ← Category.assoc, hl]
      exact ProjSpace.projectiveLinePolynomialChart_comp_π K⟩
  have hcoordinate : (p RatFunc.X)⁻¹ = P.ffAlgEquiv RatFunc.X := by
    rw [hpX, ← map_inv₀, inv_inv]
  have hθz : θ (P.ffAlgEquiv RatFunc.X) =
      PowerSeries.C (α (P.ffAlgEquiv RatFunc.X)) + PowerSeries.X := by
    rw [← hcoordinate]
    exact hθshift
  have hcomparison := rationalFunctionTrace_affineLine_genericOpenPoint_difference
    W hW l hl G trace τAffine rfl α θ hθz
  let i : RatFunc K →ₐ[K] LaurentSeries K := α.comp P.ffAlgEquiv.toAlgHom
  have hparameterOrder : w₀.ord (algebraMap P.C.functionField C.functionField
      (p RatFunc.X)) = (e : ℤ) := by
    rw [hparameterNative]
    exact hcontact w₀ hw₀boundary
  have hram := (Place.rational_contact_ramification p w₀ e hepos hparameterOrder).2
  have hInfinity := (Place.reciprocal_contact_infinity φ hφ w₀ g e hepos
    (hcontact w₀ hw₀boundary) hφX).2.2
  have hmap (f : RatFunc K) :
      algebraMap P.C.functionField C.functionField (P.ffAlgEquiv f) = φ f := by
    change φ (P.ffAlgEquiv.symm (P.ffAlgEquiv f)) = φ f
    rw [P.ffAlgEquiv.symm_apply_apply]
  have hi (f : RatFunc K) : (LaurentSeries.orderPlace (K := K)).ord (i f) =
      (e : ℤ) * (RationalFunctionField.placeInfty K).ord f := by
    rw [LaurentSeries.orderPlace_ord]
    change (α (P.ffAlgEquiv f)).order = _
    calc
      _ = (e : ℤ) * (w₀.restrict P.C.functionField).ord (P.ffAlgEquiv f) :=
        hαorder _
      _ = w₀.ord (algebraMap P.C.functionField C.functionField (P.ffAlgEquiv f)) := by
        rw [w₀.ord_restrict, hram]
      _ = w₀.ord (φ f) := congrArg w₀.ord (hmap f)
      _ = _ := hInfinity f
  have hAffine := AffineLineGroupFormalDifference.constant_of_integral_difference
    (commGroupPointEquiv G
      (Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K)))) τAffine)
    V hV hunit (LaurentSeries.orderPlace (K := K)) i e hi pint hred
    (hpint.trans hcomparison)
  change (l ≫ trace.1) =
    Spec.map (CommRingCat.ofHom (Polynomial.C (R := K))) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : K))) ≫
        (l ≫ trace.1) at hAffine
  obtain ⟨a, ha⟩ := exists_eq_const_of_polynomialChart G W l hl trace
    (by simpa only [Category.assoc] using hAffine)
  have hpolarPlace (w : Place K C.functionField) (hw : (M.placeEquiv.symm w).1 ∉ U) :
      w.ord (φ RatFunc.X) < 0 := by
    rw [hφX, Place.ord_inv, hcontact w hw]
    omega
  have : IsFinite (X := M.C) (Y := P.C) π := hfinπ
  have : Flat (X := M.C) (Y := P.C) π := hflatπ
  have : LocallyOfFinitePresentation (X := M.C) (Y := P.C) π := hlfpπ
  have : GeometricallyIntegral M.toBase := by
    change GeometricallyIntegral c
    infer_instance
  exact rationalFunctionTrace_reciprocal_evaluation_eq_zero_of_constant P M φ hφ
    hfiniteφ π hπ (finrankAlong K φ) hn hgeneric U hU hpolarPlace ε G q g hg₀ hφX a ha

/-- The full modulus for an actual map is realized by an effective relative
Cartier divisor on the same curve. Its complement lies in the original
domain, and the resulting morphism is the original restriction. -/
theorem exists_group_regularMapHasModulus
    {K : Type u} [Field K] [IsAlgClosed K]
    {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (.of K)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    (U : C.Opens) (hU : (U : Set C).Nonempty)
    (G : CommGrp (Over (Spec (.of K)))) [IsSeparated G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (q : SchemeHomOver (U.ι ≫ c) G.X.hom) :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    let M := CurveModel.ofSmoothProperCurve c
    ∃ (d : ℕ) (D : RelEffCartierDiv c d (𝟙 (Spec (.of K))))
      (hDU : modulusComplement (modulusCurveMap D) ≤ U),
      M.regularMapHasModulus D G
        ⟨C.homOfLE hDU ≫ q.1, by
          change (C.homOfLE hDU ≫ q.1) ≫ G.X.hom =
            (modulusComplement (modulusCurveMap D)).ι ≫ c
          calc
            _ = C.homOfLE hDU ≫ (q.1 ≫ G.X.hom) := Category.assoc _ _ _
            _ = C.homOfLE hDU ≫ (U.ι ≫ c) :=
              congrArg (fun f => C.homOfLE hDU ≫ f) q.2
            _ = (C.homOfLE hDU ≫ U.ι) ≫ c := (Category.assoc _ _ _).symm
            _ = _ := congrArg (fun f => f ≫ c) (Scheme.homOfLE_ι C hDU)⟩ := by
  intro algC M
  obtain ⟨E, hboundary, hE⟩ := exists_group_regularMap_modulus c U hU G q
  let I := M.pointIdealProduct E
  have hI : I.IsInvertible := M.pointIdealProduct_isInvertible E
  have hIU : I.support.compl ≤ U :=
    M.pointIdealProduct_complement_le U hU E (fun w => (hboundary w).mp)
  obtain ⟨d, D, hDI⟩ := M.exists_relativeDivisor_ideal I hI
  have hDU : modulusComplement (modulusCurveMap D) ≤ U := by
    change (modulusCurveIdeal D).support.compl ≤ U
    rw [hDI]
    exact hIU
  refine ⟨d, D, hDU, ?_⟩
  apply M.regularMapHasModulus_restriction_of_values U G q D hDU
  simpa only [hDI, I, M.cartierModulus_pointIdealProduct] using hE

end AlgebraicGeometry.GeneralizedJacobian
