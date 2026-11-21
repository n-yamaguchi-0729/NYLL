/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Kummer.AbsoluteMuNKummerLinear
public import Nyll.GaloisCohomology.Kummer.Concrete.ContinuousKummerScalar
public import Nyll.GaloisCohomology.Kummer.Concrete.RootCharacters
public import Nyll.GaloisCohomology.Topology.AbsoluteGaloisMap
public import Nyll.GaloisCohomology.Topology.ContinuousCohomologyRepresentatives
public import Nyll.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.InfiniteGaloisCorrespondence
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# The absolute Kummer isomorphism with its natural action

When the exponent is nonzero in the base field, roots of units are separable.
Continuous Hilbert 90 in the actual separable closure gives surjectivity.
For injectivity, a vanishing class gives a root-of-unity correction whose
quotient with the chosen root is fixed and separable, hence lies in the base.
-/

@[expose] public section

open scoped Pointwise Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open CategoryTheory ContRepresentation TopRep KummerTheory groupCohomology Polynomial
open RamificationTheory.Field.absoluteGaloisGroup

variable (K : Type*) [Field K] (n : ℕ+)

private def absoluteToSeparable :
    Field.absoluteGaloisGroup K ≃ₜ* Gal(SeparableClosure K/K) :=
  (absoluteGaloisGroupContinuousMulEquiv K).trans (separableClosureContinuousMulEquiv K)

private def separableUnitsMap : (SeparableClosure K)ˣ →* (AlgebraicClosure K)ˣ :=
  Units.map (algebraMap (SeparableClosure K) (AlgebraicClosure K)).toMonoidHom

private theorem separableUnitsMap_injective : Function.Injective (separableUnitsMap K) :=
  Units.map_injective (algebraMap (SeparableClosure K) (AlgebraicClosure K)).injective

private theorem separableUnitsMap_smul
    (σ : Field.absoluteGaloisGroup K) (u : (SeparableClosure K)ˣ) :
    separableUnitsMap K (absoluteToSeparable K σ • u) =
      absoluteGaloisGroupContinuousMulEquiv K σ • separableUnitsMap K u := by
  let σ' := absoluteGaloisGroupContinuousMulEquiv K σ
  have h := separableClosureExtensionAlgEquiv_restricts K
    (AlgEquiv.separableClosure σ') (u : SeparableClosure K)
  rw [extension_restrictToSeparableClosure] at h
  apply Units.ext
  change (((AlgEquiv.separableClosure σ') (u : SeparableClosure K) :
    SeparableClosure K) : AlgebraicClosure K) = σ' (u : SeparableClosure K)
  exact h.symm

private theorem unit_mem_separableClosure_of_pow_eq (hn : ((n : ℕ) : K) ≠ 0)
    (x : (AlgebraicClosure K)ˣ) (a : Kˣ)
    (hx : x ^ (n : ℕ) = Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom a) :
    (x : AlgebraicClosure K) ∈ separableClosure K (AlgebraicClosure K) := by
  apply mem_separableClosure_iff.mpr
  have hpow : (x : AlgebraicClosure K) ^ (n : ℕ) =
      algebraMap K (AlgebraicClosure K) (a : K) := congrArg Units.val hx
  have hroot : aeval (x : AlgebraicClosure K) (X ^ (n : ℕ) - C (a : K)) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hpow, sub_self]
  exact (separable_X_pow_sub_C (a : K) hn a.ne_zero).of_dvd
    (minpoly.dvd K (x : AlgebraicClosure K) hroot)

private def separableUnitOfMem (x : (AlgebraicClosure K)ˣ)
    (hx : (x : AlgebraicClosure K) ∈ separableClosure K (AlgebraicClosure K)) :
    (SeparableClosure K)ˣ :=
  Units.mk0 ⟨(x : AlgebraicClosure K), hx⟩
    (fun h => x.ne_zero (congrArg Subtype.val h))

private theorem separableUnitsMap_separableUnitOfMem (x : (AlgebraicClosure K)ˣ)
    (hx : (x : AlgebraicClosure K) ∈ separableClosure K (AlgebraicClosure K)) :
    separableUnitsMap K (separableUnitOfMem K x hx) = x :=
  Units.ext rfl

private theorem exists_baseUnit_of_separable_fixed (x : (AlgebraicClosure K)ˣ)
    (hx : (x : AlgebraicClosure K) ∈ separableClosure K (AlgebraicClosure K))
    (hfix : ∀ σ : Field.absoluteGaloisGroup K,
      absoluteGaloisGroupContinuousMulEquiv K σ • x = x) :
    ∃ b : Kˣ, Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom b = x := by
  let y := separableUnitOfMem K x hx
  have hy : separableUnitsMap K y = x := separableUnitsMap_separableUnitOfMem K x hx
  have hfixed (τ : Gal(SeparableClosure K/K)) : τ (y : SeparableClosure K) = y := by
    obtain ⟨σ, rfl⟩ := (absoluteToSeparable K).surjective τ
    have h : absoluteToSeparable K σ • y = y := by
      apply separableUnitsMap_injective K
      rw [separableUnitsMap_smul, hy, hfix]
    exact congrArg Units.val h
  obtain ⟨b, hb⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed
    (k := K) (K := SeparableClosure K) (y : SeparableClosure K)).mpr hfixed
  have hb₀ : algebraMap K (AlgebraicClosure K) b = (y : SeparableClosure K).val :=
    congrArg (fun z : SeparableClosure K => z.val) hb
  have hy₀ : ((separableUnitsMap K y : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) =
      (x : AlgebraicClosure K) :=
    congrArg (fun z : (AlgebraicClosure K)ˣ => (z : AlgebraicClosure K)) hy
  have hb' : algebraMap K (AlgebraicClosure K) b = (x : AlgebraicClosure K) :=
    hb₀.trans hy₀
  have hb0 : b ≠ 0 := by
    intro hb0
    rw [hb0, map_zero] at hb'
    exact x.ne_zero hb'.symm
  exact ⟨Units.mk0 b hb0, Units.ext hb'⟩

private theorem absoluteKummerMuNRootCocycle_one (a : Kˣ) :
    absoluteKummerMuNRootCocycle K n a 1 = 0 := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change rootQuotient (K := K) (absoluteKummerMuNChosenRoot K n a)
    (absoluteGaloisGroupContinuousMulEquiv K 1) = 1
  rw [map_one, rootQuotient_one]

private theorem zeroCochain_eq_orbit
    (b : (homogeneousCochains (absoluteMuNTopRep K (n : ℕ))).X 0) :
    b = absoluteMuNHomogeneousZeroCochain K (n : ℕ) (b.1 1) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro g
  have h := congrArg (fun τ => τ g) (b.2 g)
  change absoluteMuNActionContinuousLinearMap K (n : ℕ) g (b.1 (g⁻¹ * g)) = b.1 g at h
  rw [inv_mul_cancel] at h
  exact h.symm

/-- Triviality of the natural Kummer class forces its radicand to be a
power in the base field, provided the exponent is nonzero there. -/
theorem mem_powerRange_of_absoluteKummerMuNH1Class_eq_zero
    (hn : ((n : ℕ) : K) ≠ 0) (a : Kˣ) (ha : absoluteKummerMuNH1Class K n a = 0) :
    a ∈ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range := by
  let A := absoluteMuNTopRep K (n : ℕ)
  obtain ⟨b, hb⟩ := ContinuousCohomology.exists_boundary_of_π_eq_zero A 0
    (absoluteKummerMuNHomogeneousOneCocycle K n a) ha
  let t : AbsoluteMuN K (n : ℕ) := b.1 1
  have hbOrbit : b = absoluteMuNHomogeneousZeroCochain K (n : ℕ) t :=
    zeroCochain_eq_orbit K n b
  have hvalue (σ : Field.absoluteGaloisGroup K) :
      absoluteKummerMuNRootCocycle K n a σ =
        absoluteMuNActionContinuousLinearMap K (n : ℕ) σ t - t := by
    have h := congrArg (fun q => q.1 1 σ) hb
    rw [hbOrbit, absoluteMuNHomogeneousZeroCochain_boundary_apply,
      iCycles_absoluteKummerMuNHomogeneousOneCocycle,
      absoluteKummerMuNHomogeneousOneCochain_apply,
      absoluteKummerMuNRootCocycle_one, sub_zero] at h
    have hone : absoluteMuNActionContinuousLinearMap K (n : ℕ) 1 t = t := by
      change A.ρ 1 t = t
      rw [map_one, one_apply_eq_self]
    rw [hone] at h
    exact h.symm
  let u := absoluteKummerMuNChosenRoot K n a / t.toMul.1
  have hupow : u ^ (n : ℕ) = Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom a := by
    dsimp only [u]
    rw [div_pow, absoluteKummerMuNChosenRoot_pow,
      (mem_nthRootsSubgroup_iff (AlgebraicClosure K)).mp t.toMul.property, div_one]
  have hfix (σ : Field.absoluteGaloisGroup K) :
      absoluteGaloisGroupContinuousMulEquiv K σ • u = u := by
    apply div_eq_one.mp
    change rootQuotient (K := K) (absoluteKummerMuNChosenRoot K n a / t.toMul.1)
      (absoluteGaloisGroupContinuousMulEquiv K σ) = 1
    rw [rootQuotient_div]
    apply div_eq_one.mpr
    exact congrArg (fun x : AbsoluteMuN K (n : ℕ) => x.toMul.1) (hvalue σ)
  obtain ⟨v, hv⟩ := exists_baseUnit_of_separable_fixed K u
    (unit_mem_separableClosure_of_pow_eq K n hn u a hupow) hfix
  refine ⟨v, ?_⟩
  apply Units.map_injective (algebraMap K (AlgebraicClosure K)).injective
  change Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom (v ^ (n : ℕ)) = _
  rw [map_pow, hv, hupow]

/-- The absolute Kummer map is injective on power classes. -/
theorem absoluteKummerMuNPowerClassHom_injective (hn : ((n : ℕ) : K) ≠ 0) :
    Function.Injective (absoluteKummerMuNPowerClassHom K n) := by
  apply (MonoidHom.ker_eq_bot_iff (f := absoluteKummerMuNPowerClassHom K n)).mp
  apply le_antisymm
  · intro q hq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range q
    have h : (absoluteKummerMuNPowerClassHom K n
        (QuotientGroup.mk' (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range a)).toAdd = 0 :=
      congrArg Multiplicative.toAdd (MonoidHom.mem_ker.mp hq)
    rw [absoluteKummerMuNPowerClassHom_mk] at h
    exact (QuotientGroup.eq_one_iff a).mpr
      (mem_powerRange_of_absoluteKummerMuNH1Class_eq_zero K n hn a h)
  · exact bot_le

private def muNCocycleValue (z : ContinuousCohomology.cocycles (absoluteMuNTopRep K n) 1)
    (σ : Field.absoluteGaloisGroup K) : AbsoluteMuN K (n : ℕ) :=
  ((homogeneousCochains (absoluteMuNTopRep K n)).iCycles 1 z).1 1 σ

private theorem muNCocycle_eq_difference
    (z : ContinuousCohomology.cocycles (absoluteMuNTopRep K n) 1)
    (g h : Field.absoluteGaloisGroup K) :
    ((homogeneousCochains (absoluteMuNTopRep K n)).iCycles 1 z).1 g h =
      muNCocycleValue K n z h - muNCocycleValue K n z g := by
  let A := absoluteMuNTopRep K (n : ℕ)
  let C := homogeneousCochains A
  let c := C.iCycles 1 z
  have hz := ConcreteCategory.congr_hom (C.iCycles_d 1 2) z
  have hd := congrArg (fun τ => τ 1 g h) (homogeneousCochains.d_apply A 1 c)
  have hz' := congrArg (fun τ => τ.1 1 g h) hz
  change ((C.d 1 2).hom c).1 1 g h = 0 at hz'
  rw [hd] at hz'
  simp only [d_succ, d_zero, TopRep.hom_sub, ContIntertwiningMap.sub_apply,
    coind₁ι_toFun, coind₁Map_toFun, ContinuousMap.const_apply, ContinuousMap.comp_apply,
    ConcreteCategory.hom_ofHom, ContinuousMap.sub_apply] at hz'
  change c.1 g h - (c.1 1 h - c.1 1 g) = 0 at hz'
  exact sub_eq_zero.mp hz'

private theorem muNCocycleValue_mul
    (z : ContinuousCohomology.cocycles (absoluteMuNTopRep K n) 1)
    (g h : Field.absoluteGaloisGroup K) :
    muNCocycleValue K n z (g * h) =
      absoluteMuNActionContinuousLinearMap K (n : ℕ) g (muNCocycleValue K n z h) +
        muNCocycleValue K n z g := by
  let c := (homogeneousCochains (absoluteMuNTopRep K n)).iCycles 1 z
  have hact := congrArg (fun τ => τ g (g * h)) (c.2 g)
  change absoluteMuNActionContinuousLinearMap K (n : ℕ) g
      (c.1 (g⁻¹ * g) (g⁻¹ * (g * h))) = c.1 g (g * h) at hact
  rw [inv_mul_cancel, inv_mul_cancel_left] at hact
  have hd := muNCocycle_eq_difference K n z g (g * h)
  change c.1 g (g * h) = _ at hd
  rw [← hact] at hd
  exact (eq_sub_iff_add_eq.mp hd).symm

private theorem exists_absolute_radical_of_muNCocycle (hn : ((n : ℕ) : K) ≠ 0)
    (z : ContinuousCohomology.cocycles (absoluteMuNTopRep K n) 1) :
    ∃ (a : Kˣ) (u : (AlgebraicClosure K)ˣ),
      u ^ (n : ℕ) = Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom a ∧
        ∀ σ : Field.absoluteGaloisGroup K,
          rootQuotient (K := K) u (absoluteGaloisGroupContinuousMulEquiv K σ) =
            (muNCocycleValue K n z σ).toMul.1 := by
  let e := absoluteToSeparable K
  let c := muNCocycleValue K n z
  have hcSep (σ : Gal(SeparableClosure K/K)) :
      ((c (e.symm σ)).toMul.1 : AlgebraicClosure K) ∈
        separableClosure K (AlgebraicClosure K) := by
    apply unit_mem_separableClosure_of_pow_eq K n hn _ (1 : Kˣ)
    rw [map_one, (mem_nthRootsSubgroup_iff (AlgebraicClosure K)).mp
      (c (e.symm σ)).toMul.property]
  let d (σ : Gal(SeparableClosure K/K)) : (SeparableClosure K)ˣ :=
    separableUnitOfMem K (c (e.symm σ)).toMul.1 (hcSep σ)
  have hmap (σ : Gal(SeparableClosure K/K)) :
      separableUnitsMap K (d σ) = (c (e.symm σ)).toMul.1 :=
    separableUnitsMap_separableUnitOfMem K _ (hcSep σ)
  have hd : IsMulCocycle₁ d := by
    intro σ τ
    apply separableUnitsMap_injective K
    have hact : separableUnitsMap K (σ • d τ) =
        absoluteGaloisGroupContinuousMulEquiv K (e.symm σ) • separableUnitsMap K (d τ) := by
      calc
        _ = separableUnitsMap K (e (e.symm σ) • d τ) := by rw [e.apply_symm_apply]
        _ = _ := separableUnitsMap_smul K (e.symm σ) (d τ)
    simp only [hmap, map_mul, hact]
    exact congrArg (fun x : AbsoluteMuN K (n : ℕ) => x.toMul.1)
      (muNCocycleValue_mul K n z (e.symm σ) (e.symm τ))
  have hcCont : Continuous c :=
    (((homogeneousCochains (absoluteMuNTopRep K n)).iCycles 1 z).1 1).continuous
  have hdLC : IsLocallyConstant d := by
    have h := ((IsLocallyConstant.iff_continuous c).mpr hcCont).comp_continuous e.symm.continuous
    apply (IsLocallyConstant.iff_exists_open _).mpr
    intro σ
    obtain ⟨V, hV, hσ, hconst⟩ := h.exists_open σ
    refine ⟨V, hV, hσ, ?_⟩
    intro τ hτ
    apply separableUnitsMap_injective K
    rw [hmap, hmap]
    exact congrArg (fun x : AbsoluteMuN K (n : ℕ) => x.toMul.1) (hconst τ hτ)
  have hdPow (σ : Gal(SeparableClosure K/K)) : d σ ^ (n : ℕ) = 1 := by
    apply separableUnitsMap_injective K
    rw [map_pow, map_one, hmap]
    exact (mem_nthRootsSubgroup_iff (AlgebraicClosure K)).mp (c (e.symm σ)).toMul.property
  obtain ⟨a, β, hβ, hq⟩ :=
    exists_scalar_radical_of_isLocallyConstant_mulCocycle (n : ℕ) d hd hdLC hdPow
  refine ⟨a, separableUnitsMap K β, ?_, ?_⟩
  · calc
      separableUnitsMap K β ^ (n : ℕ) = separableUnitsMap K (β ^ (n : ℕ)) :=
        (map_pow (separableUnitsMap K) β (n : ℕ)).symm
      _ = separableUnitsMap K (Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a) :=
        congrArg (separableUnitsMap K) hβ
      _ = Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom a := Units.ext rfl
  · intro σ
    change absoluteGaloisGroupContinuousMulEquiv K σ • separableUnitsMap K β /
      separableUnitsMap K β = (c σ).toMul.1
    rw [← separableUnitsMap_smul, ← _root_.map_div]
    change separableUnitsMap K (rootQuotient (K := K) β (e σ)) = _
    rw [hq, hmap, e.symm_apply_apply]

/-- Every degree-one class of the natural roots-of-unity representation
comes from an actual base-field unit. -/
theorem absoluteKummerMuNPowerClassHom_surjective (hn : ((n : ℕ) : K) ≠ 0) :
    Function.Surjective (absoluteKummerMuNPowerClassHom K n) := by
  let A := absoluteMuNTopRep K (n : ℕ)
  let C := homogeneousCochains A
  intro q
  obtain ⟨z, hz⟩ := ContinuousCohomology.π_surjective A 1 q.toAdd
  obtain ⟨a, u, hu, hq⟩ := exists_absolute_radical_of_muNCocycle K n hn z
  let r := absoluteKummerMuNChosenRoot K n a
  let t : AbsoluteMuN K (n : ℕ) := Additive.ofMul
    ⟨u / r, div_mem_nthRootsSubgroup_of_pow_eq_pow (AlgebraicClosure K)
      (hu.trans (absoluteKummerMuNChosenRoot_pow K n a).symm)⟩
  have hvalue (σ : Field.absoluteGaloisGroup K) :
      muNCocycleValue K n z σ - absoluteKummerMuNRootCocycle K n a σ =
        absoluteMuNActionContinuousLinearMap K (n : ℕ) σ t - t := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change (muNCocycleValue K n z σ).toMul.1 /
      rootQuotient (K := K) r (absoluteGaloisGroupContinuousMulEquiv K σ) =
        rootQuotient (K := K) (u / r) (absoluteGaloisGroupContinuousMulEquiv K σ)
    rw [← hq σ, rootQuotient_div]
  let b := absoluteMuNHomogeneousZeroCochain K (n : ℕ) t
  have hdiff : z - absoluteKummerMuNHomogeneousOneCocycle K n a = (C.toCycles 0 1).hom b := by
    let F := forget₂ (TopModuleCat (ZMod (n : ℕ))) (ModuleCat (ZMod (n : ℕ)))
    apply (ModuleCat.mono_iff_injective (F.map (C.iCycles 1))).mp inferInstance
    change (C.iCycles 1).hom _ = (C.iCycles 1).hom _
    have htoCycles : (C.iCycles 1).hom ((C.toCycles 0 1).hom b) = (C.d 0 1).hom b :=
      ConcreteCategory.congr_hom (C.toCycles_i 0 1) b
    rw [map_sub, iCycles_absoluteKummerMuNHomogeneousOneCocycle, htoCycles]
    apply Subtype.ext
    ext g h
    change (C.iCycles 1 z).1 g h - (absoluteKummerMuNHomogeneousOneCochain K n a).1 g h =
      ((C.d 0 1).hom b).1 g h
    rw [muNCocycle_eq_difference, absoluteKummerMuNHomogeneousOneCochain_apply,
      absoluteMuNHomogeneousZeroCochain_boundary_apply]
    calc
      _ = (muNCocycleValue K n z h - absoluteKummerMuNRootCocycle K n a h) -
          (muNCocycleValue K n z g - absoluteKummerMuNRootCocycle K n a g) := by abel
      _ = _ := by
        rw [hvalue h, hvalue g]
        abel
  have hboundary : ContinuousCohomology.π A 1 ((C.toCycles 0 1).hom b) = 0 :=
    ConcreteCategory.congr_hom (C.toCycles_comp_homologyπ 0 1) b
  have h := congrArg (ContinuousCohomology.π A 1) hdiff
  rw [map_sub, hboundary] at h
  refine ⟨QuotientGroup.mk' (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range a, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [absoluteKummerMuNPowerClassHom_mk, ← hz]
  exact (sub_eq_zero.mp h).symm

/-- The Kummer isomorphism uses the natural Galois action on the roots of
unity and holds in every characteristic prime to the exponent. -/
noncomputable def absoluteKummerMuNPowerClassEquiv (hn : ((n : ℕ) : K) ≠ 0) :
    (Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) ≃*
      Multiplicative (continuousCohomology 1 (absoluteMuNTopRep K (n : ℕ))) :=
  MulEquiv.ofBijective (absoluteKummerMuNPowerClassHom K n)
    ⟨absoluteKummerMuNPowerClassHom_injective K n hn,
      absoluteKummerMuNPowerClassHom_surjective K n hn⟩

/-- On power-class representatives the isomorphism evaluates to the
natural root-quotient class. -/
@[simp]
theorem absoluteKummerMuNPowerClassEquiv_mk (hn : ((n : ℕ) : K) ≠ 0) (a : Kˣ) :
    (absoluteKummerMuNPowerClassEquiv K n hn
      (QuotientGroup.mk' (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range a)).toAdd =
        absoluteKummerMuNH1Class K n a :=
  absoluteKummerMuNPowerClassHom_mk K n a

end ClassFieldTower.Martinet.Shafarevich
