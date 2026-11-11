/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.ClassGroup.KummerClasses
public import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
public import Nyll.AlgebraicCurves.Divisors.Maps.Semilinear
public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.ConstantExtension.SemilinearAction
public import Nyll.AlgebraicCurves.Models.ConstantExtension.SemilinearFunctionField
public import Nyll.AlgebraicCurves.Models.Kummer.CurveCoverCharacterProduct
public import Nyll.AlgebraicCurves.Models.Kummer.DivisorClassCohomologyInjection
public import Nyll.AlgebraicCurves.Models.Kummer.SemilinearGenericCharacter
public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Nyll.EtaleCohomology.Frobenius.ArithmeticComparison
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1Comparison
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1PullbackComposition
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericPointCharacterDetection
public import Nyll.EtaleFundamentalGroups.Cohomology.H1Additivity
public import Nyll.EtaleFundamentalGroups.Cohomology.H1Character
public import Nyll.EtaleFundamentalGroups.Cohomology.H1FieldSourceSchemeConjugation
public import Nyll.EtaleFundamentalGroups.Cohomology.H1Naturality
public import Nyll.EtaleFundamentalGroups.Cohomology.SchemePullback
public import Nyll.EtaleFundamentalGroups.GeometricFiber.BasePoint
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGalois
public import Nyll.EtaleFundamentalGroups.GeometricFiber.Functoriality
public import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugation
public import Nyll.SchemeTheory.LocalGeometry.SmoothStalks
public import Nyll.SchemeTheory.FunctionFields.OpenImmersion
public import Nyll.SchemeTheory.Morphisms.ConstantTwist
public import Nyll.SchemeTheory.Morphisms.FiniteFieldConstantAction
public import Nyll.SchemeTheory.Normalization.Normal
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Proper Kummer comparison and geometric Frobenius

The original proper Kummer map respects actual coefficient twists, with the
action on roots of unity retained. On a finite-field constant extension,
the native geometric Frobenius pullback therefore corresponds to `q` times
inverse arithmetic Frobenius on the actual torsion divisor classes.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open EtaleFundamentalGroups.Cohomology EtaleCohomology

namespace AlgebraicCurve.CurveModel

section Kummer

variable {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  [Algebra.EssFiniteType K F] [IsCurveOver K F]
  (M : CurveModel K F) (n : ℕ+) (hn : IsUnit ((n : ℕ) : K))

private theorem h1Character_kummerTorsionCohomology
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ M.C)
    (x : Pic0.torsion K F n) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    h1Character (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) xi
        (M.kummerTorsionCohomology n hn xi x) =
      M.kummerTorsionCharacter n hn xi (Multiplicative.ofAdd x) := by
  intro tμ dμ
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  exact congrArg Additive.toMul ((finiteH1CharacterEquiv A xi).apply_symm_apply
    (Additive.ofMul (M.kummerTorsionCharacter n hn xi (Multiplicative.ofAdd x))))

private theorem kummerTorsionCohomology_basePoint
    {Ω Ω' : Type} [Field Ω] [IsSepClosed Ω] [Field Ω'] [IsSepClosed Ω']
    (xi : Spec (.of Ω) ⟶ M.C) (eta : Spec (.of Ω') ⟶ M.C)
    (x : Pic0.torsion K F n) :
    M.kummerTorsionCohomology n hn xi x = M.kummerTorsionCohomology n hn eta x := by
  have : IsIntegral M.C := M.isIntegral
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  have : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  let t : FiniteEtale.fiber eta ≅ FiniteEtale.fiber xi :=
    Classical.choice (FiniteEtale.nonempty_fiber_iso eta xi)
  let b := FiniteEtale.fundamentalGroupIsoOfFiberIso eta xi t
  apply h1Character_injective A xi
  apply ContinuousMonoidHom.ext
  intro γ
  obtain ⟨ρ, rfl⟩ := b.surjective γ
  have hb := DFunLike.congr_fun
    (h1Character_basePoint A eta xi t (M.kummerTorsionCohomology n hn eta x)) ρ
  change h1Character A xi (M.kummerTorsionCohomology n hn eta x) (b ρ) =
    h1Character A eta (M.kummerTorsionCohomology n hn eta x) ρ at hb
  have hm : M.kummerTorsionCharacter n hn xi (Multiplicative.ofAdd x) (b ρ) =
      M.kummerTorsionCharacter n hn eta (Multiplicative.ofAdd x) ρ := by
    obtain ⟨u, hu⟩ := Pic0.kummerClass_surjective n (Multiplicative.ofAdd x)
    rw [← hu, M.kummerTorsionCharacter_kummerClass,
      M.kummerTorsionCharacter_kummerClass]
    exact M.kummerMonodromyCharacter_basePoint_apply n hn u eta xi t ρ
  exact (DFunLike.congr_fun (h1Character_kummerTorsionCohomology M n hn xi x) (b ρ)).trans
    (hm.trans ((DFunLike.congr_fun
      (h1Character_kummerTorsionCohomology M n hn eta x) ρ).symm.trans hb.symm))

private theorem kummerTorsionCohomology_semilinear
    (θ : M.C ≅ M.C) (g : SemilinearAut K F)
    (hg : ∀ (U : M.C.Opens) [Nonempty (Scheme.Opens.toScheme U)]
      [Nonempty (Scheme.Opens.toScheme (θ.hom ⁻¹ᵁ U))] (t : Γ(M.C, U)),
      g • M.ffEquiv.symm (M.C.germToFunctionField U t) =
        M.ffEquiv.symm (M.C.germToFunctionField (θ.hom ⁻¹ᵁ U) ((θ.hom.app U).hom t)))
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ M.C)
    (x : Pic0.torsion K F n) :
    let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
    let α : A ⟶ A := AddCommGrpCat.ofHom
      (restrictRootsOfUnity (SemilinearAut.baseAut g).toRingHom (n : ℕ)).toAdditive
    Sheaf.H.map ((constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{0}).map α) 1
        (constantCohomologyPullback θ.hom A 1 (M.kummerTorsionCohomology n hn xi x)) =
      M.kummerTorsionCohomology n hn xi (g • x) := by
  intro A α
  have : IsIntegral M.C := M.isIntegral
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral M.C := IsNormalIntegral.of_stalks M.C
    (fun z => (Smooth.isDomain_and_isIntegrallyClosed_stalk M.toBase z).2)
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  have : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  let Ωg := SeparableClosure M.C.functionField
  have : IsSepClosure M.C.functionField Ωg :=
    separableClosure.isSepClosure M.C.functionField (AlgebraicClosure M.C.functionField)
  let η := Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ωg))
  let j := M.C.fromSpecStalk (genericPoint M.C)
  let p := η ≫ j
  rw [kummerTorsionCohomology_basePoint M n hn xi p x,
    kummerTorsionCohomology_basePoint M n hn xi p (g • x)]
  let φ := θ.hom.functionFieldRingEquivOfIsOpenImmersion
  have hφ (z : F) : φ (M.ffEquiv z) = M.ffEquiv (SemilinearAut.toRingAut g z) :=
    M.functionFieldRingEquiv_semilinear θ g hg z
  obtain ⟨a, ha, _, hpull⟩ := exists_h1Character_genericSource_schemeConjugate θ Ωg A
  let J := FiniteEtale.fieldSourceAbsoluteGaloisHom M.C.functionField Ωg j
  have hJ (ρ : Gal(Ωg/M.C.functionField)) :
      J ρ = FiniteEtale.fundamentalGroupHom j η
        (toAut (FiniteEtale.fiber η) (Ωg ≃ₐ[M.C.functionField] Ωg) ρ) := by
    change FiniteEtale.fundamentalGroupHom j η
        (toAutHomeo (FiniteEtale.fiber η) (Ωg ≃ₐ[M.C.functionField] Ωg) ρ) = _
    exact congrArg (FiniteEtale.fundamentalGroupHom j η) (toAutHomeo_apply _ ρ)
  have hsurj : Function.Surjective J := by
    intro γ
    obtain ⟨ρ, hρ⟩ := FiniteEtale.genericFieldAction_surjective M.C Ωg γ
    exact ⟨ρ, (hJ ρ).trans hρ⟩
  apply h1Character_injective A p
  apply ContinuousMonoidHom.ext
  intro γ
  obtain ⟨τ, rfl⟩ := hsurj γ
  obtain ⟨ρ, rfl⟩ := (KummerTheory.semilinearGaloisConjugateEquiv φ a ha).surjective τ
  change h1Character A p
      (Sheaf.H.map ((constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{0}).map α) 1
        (constantCohomologyPullback θ.hom A 1 (M.kummerTorsionCohomology n hn p x)))
      (J (KummerTheory.semilinearGaloisConjugate φ a ha ρ)) =
    h1Character A p (M.kummerTorsionCohomology n hn p (g • x))
      (J (KummerTheory.semilinearGaloisConjugate φ a ha ρ))
  have hc := DFunLike.congr_fun
    (h1Character_naturality α p
      (constantCohomologyPullback θ.hom A 1 (M.kummerTorsionCohomology n hn p x)))
    (J (KummerTheory.semilinearGaloisConjugate φ a ha ρ))
  refine hc.symm.trans ?_
  change restrictRootsOfUnity (SemilinearAut.baseAut g).toRingHom (n : ℕ)
      (h1Character A p
        (constantCohomologyPullback θ.hom A 1 (M.kummerTorsionCohomology n hn p x))
        (J (KummerTheory.semilinearGaloisConjugate φ a ha ρ))) =
    h1Character A p (M.kummerTorsionCohomology n hn p (g • x))
      (J (KummerTheory.semilinearGaloisConjugate φ a ha ρ))
  rw [hpull, h1Character_kummerTorsionCohomology, h1Character_kummerTorsionCohomology]
  rw [hJ, hJ]
  apply rootsOfUnity.coe_injective
  exact (M.kummerTorsionCharacter_generic_semilinear n hn g φ hφ a ha x ρ).symm

end Kummer

section ConstantExtension

variable {k K F : Type} [Field k] [Field K] [IsAlgClosed K] [Algebra k K]
  [Field F] [Algebra K F] [Algebra.EssFiniteType K F] [IsCurveOver K F]
  (M : CurveModel K F) {C : Scheme} (c : C ⟶ Spec (.of k))
  (e : M.C ≅ pullback c (SmoothProperCurve.specMap k K))
  (he : e.hom ≫ pullback.snd c (SmoothProperCurve.specMap k K) = M.toBase)
  (n : ℕ+) (hn : IsUnit ((n : ℕ) : K))
  {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ M.C)

/-- The actual coefficient twist preserves the proper Kummer comparison
after applying its specified action on roots-of-unity coefficients. -/
theorem kummerTorsionCohomology_constantTwist
    (σ : K ≃ₐ[k] K) (x : Pic0.torsion K F n) :
    let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
    let α : A ⟶ A := AddCommGrpCat.ofHom
      (restrictRootsOfUnity σ.toRingHom (n : ℕ)).toAdditive
    Sheaf.H.map ((constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{0}).map α) 1
        (constantCohomologyPullback (M.coefficientIso c e σ).hom A 1
          (M.kummerTorsionCohomology n hn xi x)) =
      M.kummerTorsionCohomology n hn xi (M.constantSemilinearAction c e he σ • x) := by
  intro A α
  exact kummerTorsionCohomology_semilinear M n hn (M.coefficientIso c e σ)
    (M.constantSemilinearAction c e he σ) (M.constantSemilinearAction_germ c e he σ) xi x

variable [Fintype k] [Algebra.IsAlgebraic k K]

/-- Inverse arithmetic coefficient twisting acts on proper Kummer H¹ by
`q` times inverse arithmetic action on the original torsion divisor classes. -/
theorem kummerTorsionCohomology_inverseArithmetic
    (x : Pic0.torsion K F n) :
    let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k K
    let g := M.constantSemilinearAction c e he σ
    let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
    constantCohomologyPullback (M.coefficientIso c e σ.symm).hom A 1
        (M.kummerTorsionCohomology n hn xi x) =
      M.kummerTorsionCohomology n hn xi ((Fintype.card k) • (g⁻¹ • x)) := by
  intro σ g A
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let α : A ⟶ A := AddCommGrpCat.ofHom
    (restrictRootsOfUnity σ.symm.toRingHom (n : ℕ)).toAdditive
  let β : A ⟶ A := AddCommGrpCat.ofHom
    (restrictRootsOfUnity σ.toRingHom (n : ℕ)).toAdditive
  let H := constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{0} ⋙
    Sheaf.functorH M.C.smallEtaleTopology 1
  have hαβ : α ≫ β = 𝟙 A := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro ζ
    apply Additive.toMul.injective
    apply rootsOfUnity.coe_injective
    let μ : rootsOfUnity (n : ℕ) K :=
      Additive.toMul (show Additive (rootsOfUnity (n : ℕ) K) from ζ)
    exact σ.apply_symm_apply ((μ : Kˣ) : K)
  have hβ : β = (Fintype.card k) • 𝟙 A := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro ζ
    apply Additive.toMul.injective
    apply rootsOfUnity.coe_injective
    let μ : rootsOfUnity (n : ℕ) K :=
      Additive.toMul (show Additive (rootsOfUnity (n : ℕ) K) from ζ)
    exact congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic k K)
      ((μ : Kˣ) : K)
  have hcancel (z : H.obj A) : H.map β (H.map α z) = z := by
    change (H.map α ≫ H.map β) z = z
    rw [← H.map_comp, hαβ, H.map_id]
    rfl
  have hq (z : H.obj A) : H.map β z = (Fintype.card k) • z := by
    rw [hβ, Functor.map_nsmul, H.map_id]
    rfl
  have hs := M.kummerTorsionCohomology_constantTwist c e he n hn xi σ.symm x
  have hginv : M.constantSemilinearAction c e he σ.symm = g⁻¹ :=
    map_inv (M.constantSemilinearAction c e he) σ
  change H.map α
      (constantCohomologyPullback (M.coefficientIso c e σ.symm).hom A 1
        (M.kummerTorsionCohomology n hn xi x)) =
    M.kummerTorsionCohomology n hn xi (M.constantSemilinearAction c e he σ.symm • x) at hs
  rw [hginv] at hs
  let z : H.obj A :=
    constantCohomologyPullback (M.coefficientIso c e σ.symm).hom A 1
      (M.kummerTorsionCohomology n hn xi x)
  let y : H.obj A := M.kummerTorsionCohomology n hn xi (g⁻¹ • x)
  have h : H.map β (H.map α z) = H.map β y :=
    congrArg (fun w : H.obj A => H.map β w) hs
  exact (hcancel z).symm.trans (h.trans ((hq y).trans
    ((M.kummerTorsionCohomology n hn xi).map_nsmul (Fintype.card k)
      (g⁻¹ • x)).symm))

end ConstantExtension

section Frobenius

variable {k K F : Type} [Field k] [Fintype k] [Field K] [IsAlgClosed K]
  [Algebra k K] [Algebra.IsAlgebraic k K]
  [Field F] [Algebra K F] [Algebra.EssFiniteType K F] [IsCurveOver K F]
  (M : CurveModel K F) (C : Scheme) [C.Over (Spec (.of k))]
  (e : M.C ≅ pullback (C ↘ Spec (.of k)) (SmoothProperCurve.specMap k K))
  (he : e.hom ≫ pullback.snd (C ↘ Spec (.of k)) (SmoothProperCurve.specMap k K) = M.toBase)
  (n : ℕ+) (hn : IsUnit ((n : ℕ) : K))
  {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ M.C)

/-- On the literal constant extension, native geometric Frobenius on H¹
corresponds under the original proper Kummer comparison to `q` times the
inverse arithmetic action on torsion divisor classes. -/
theorem kummerTorsionCohomology_geometricFrobenius
    (x : Pic0.torsion K F n) :
    let c := C ↘ Spec (.of k)
    let Y := pullback c (SmoothProperCurve.specMap k K)
    let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
    let κ := fun y : Pic0.torsion K F n =>
      constantCohomologyPullback e.inv A 1 (M.kummerTorsionCohomology n hn xi y)
    let g := M.constantSemilinearAction c e he
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K)
    Sheaf.H.map ((etaleAbelianPullbackConstantIso
        (Scheme.constantBaseChangeFrobenius k K C)).hom.app A) 1
        (etaleAbelianCohomologyPullbackMap (Scheme.constantBaseChangeFrobenius k K C)
          ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{0}).obj A) 1 (κ x)) =
      κ ((Fintype.card k) • (g⁻¹ • x)) := by
  intro c Y A κ g
  have : IsIntegral M.C := M.isIntegral
  have : IsIntegral Y := IsIntegral.of_isIso e.hom
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k K
  let t := Scheme.constantFieldTwist k K C σ.symm
  let θ := (M.coefficientIso c e σ.symm).hom
  have htwist : (Scheme.constantTwist c σ.symm).hom = t := by
    apply pullback.hom_ext
    · exact (Scheme.constantTwist_fst c σ.symm).trans
        (Scheme.constantFieldTwist_fst k K C σ.symm).symm
    · exact (Scheme.constantTwist_snd c σ.symm).trans
        (Scheme.constantFieldTwist_snd k K C σ.symm).symm
  have hθ : θ ≫ e.hom = e.hom ≫ t := by
    change (e.hom ≫ (Scheme.constantTwist c σ.symm).hom ≫ e.inv) ≫ e.hom = _
    rw [Category.assoc, Category.assoc, e.inv_hom_id, Category.comp_id, htwist]
  have hsq : t ≫ e.inv = e.inv ≫ θ := by
    have h := congrArg (fun f : M.C ⟶ Y => e.inv ≫ f ≫ e.inv) hθ
    simpa only [Category.assoc, e.hom_inv_id, Category.comp_id,
      e.inv_hom_id_assoc] using h.symm
  have hgeom := geometricFrobenius_eq_inverseArithmetic_on_constantCohomology
    k K C A 1 (κ x)
  change constantCohomologyPullback (Scheme.constantBaseChangeFrobenius k K C) A 1
      (κ x) = constantCohomologyPullback t A 1 (κ x) at hgeom
  change constantCohomologyPullback (Scheme.constantBaseChangeFrobenius k K C) A 1
      (κ x) = κ ((Fintype.card k) • (g⁻¹ • x))
  rw [hgeom]
  change constantCohomologyPullback t A 1
      (constantCohomologyPullback e.inv A 1 (M.kummerTorsionCohomology n hn xi x)) = _
  rw [← constantFiniteH1Pullback_comp t e.inv (xi ≫ e.hom) A,
    hsq, constantFiniteH1Pullback_comp e.inv θ (xi ≫ e.hom) A]
  exact congrArg (constantCohomologyPullback e.inv A 1)
    (M.kummerTorsionCohomology_inverseArithmetic c e he n hn xi x)

end Frobenius

end AlgebraicCurve.CurveModel
