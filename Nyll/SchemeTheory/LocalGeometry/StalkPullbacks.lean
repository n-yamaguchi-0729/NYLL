/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Tactic.ApplyFun
public import Mathlib.Tactic.Set
public import Nyll.SchemeTheory.Modules.Sections.SectionsAlgebra
public import Nyll.SchemeTheory.RingTheory.Differentials.Basic
public import Nyll.SchemeTheory.LocalGeometry.StalkPullbackLocalization

/-!
# Stalks and cotangent modules of fibre products

Tensor-product localizations identify the stalk of a fibre product. The general maximal-ideal
formula at a pair of sections supplies both affine and unrestricted inclusion corollaries.
The final comparison identifies the corresponding localized Kähler differentials.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_stalk.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.StalkPullbackLocalizations

universe u

open TensorProduct

namespace RightTensorLocalization

variable {A S R L : Type*} [CommRing A] [CommRing S] [CommRing R] [CommRing L]
  [Algebra A S] [Algebra A R] [Algebra A L] [Algebra R L] [IsScalarTower A R L]

/-- The coefficient map on the right factor of a tensor product. -/
@[reducible] noncomputable def tensorAlgebra : Algebra (S ⊗[A] R) (S ⊗[A] L) :=
  (Algebra.TensorProduct.map (AlgHom.id A S) (IsScalarTower.toAlgHom A R L)).toRingHom.toAlgebra

attribute [local instance] tensorAlgebra

theorem algebraMap_tensor_tmul (s : S) (r : R) :
    algebraMap (S ⊗[A] R) (S ⊗[A] L) (s ⊗ₜ r) = s ⊗ₜ algebraMap R L r := rfl

theorem isScalarTower_tensor : IsScalarTower S (S ⊗[A] R) (S ⊗[A] L) :=
  IsScalarTower.of_algebraMap_eq (R := S) (S := S ⊗[A] R) (A := S ⊗[A] L) fun s => by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self,
      RingHom.id_apply, algebraMap_tensor_tmul, map_one]

theorem isLocalization_tensor (M : Submonoid R) [IsLocalization M L] :
    IsLocalization (M.map (Algebra.TensorProduct.includeRight (R := A) (A := S) (B := R))) (S ⊗[A]
        L) := by
  have : IsScalarTower S (S ⊗[A] R) (S ⊗[A] L) :=
    isScalarTower_tensor (A := A) (S := S) (R := R) (L := L)
  refine IsLocalization.tensorProduct_tensorProduct_right A S M L ?_
  ext r
  rfl

theorem core (𝔭 : Ideal R) [𝔭.IsPrime] [IsLocalization.AtPrime L 𝔭]
    (𝔔 : Ideal (S ⊗[A] R)) [h𝔔 : 𝔔.IsPrime]
    (hQp : 𝔔.comap (Algebra.TensorProduct.includeRight (R := A) (A := S) (B := R)).toRingHom = 𝔭)
    (Tq : Type*) [CommRing Tq] [Algebra (S ⊗[A] R) Tq] [IsLocalization.AtPrime Tq 𝔔]
    (φ : L →+* Tq) (hφ : ∀ r : R, φ (algebraMap R L r) = algebraMap (S ⊗[A] R) Tq (1 ⊗ₜ r)) :
    ∃ (𝔮 : Ideal (S ⊗[A] L)) (_ : 𝔮.IsPrime) (e : Tq ≃+* Localization.AtPrime 𝔮),
      (∀ s : S, e (algebraMap (S ⊗[A] R) Tq (s ⊗ₜ[A] (1 : R))) =
        algebraMap (S ⊗[A] L) (Localization.AtPrime 𝔮) (s ⊗ₜ[A] 1)) ∧
      (∀ l : L, e (φ l) = algebraMap (S ⊗[A] L) (Localization.AtPrime 𝔮) ((1 : S) ⊗ₜ[A] l)) := by
  have : IsScalarTower S (S ⊗[A] R) (S ⊗[A] L) :=
    isScalarTower_tensor (A := A) (S := S) (R := R) (L := L)
  set T := S ⊗[A] R
  set M : Submonoid T := 𝔭.primeCompl.map (Algebra.TensorProduct.includeRight (R := A) (A := S) (B
      := R)) with hM
  have hloc : IsLocalization M (S ⊗[A] L) := isLocalization_tensor 𝔭.primeCompl
  have hdisj : Disjoint (M : Set T) (𝔔 : Set T) := by
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hrQ
    apply hr
    rw [← hQp]
    exact hrQ
  let 𝔮 : Ideal (S ⊗[A] L) := 𝔔.map (algebraMap T (S ⊗[A] L))
  have h𝔮 : 𝔮.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M (S ⊗[A] L) 𝔔 h𝔔 hdisj
  have hunder : 𝔮.comap (algebraMap T (S ⊗[A] L)) = 𝔔 :=
    IsLocalization.under_map_of_isPrime_disjoint M (S ⊗[A] L) h𝔔 hdisj
  have : IsLocalization.AtPrime (Localization.AtPrime 𝔮) (𝔮.comap (algebraMap T (S ⊗[A] L))) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M (Localization.AtPrime 𝔮) 𝔮
  have hN : 𝔔.primeCompl = (Ideal.comap (algebraMap T (S ⊗[A] L)) 𝔮).primeCompl := by
    ext x
    change x ∉ 𝔔 ↔ x ∉ Ideal.comap (algebraMap T (S ⊗[A] L)) 𝔮
    rw [hunder]
  have : IsLocalization.AtPrime (Localization.AtPrime 𝔮) 𝔔 := by
    change IsLocalization 𝔔.primeCompl (Localization.AtPrime 𝔮)
    rw [hN]
    exact this
  let e : Tq ≃ₐ[T] Localization.AtPrime 𝔮 := IsLocalization.algEquiv 𝔔.primeCompl Tq
      (Localization.AtPrime 𝔮)
  refine ⟨𝔮, h𝔮, e.toRingEquiv, ?_, ?_⟩
  · intro s
    change e (algebraMap T Tq (s ⊗ₜ[A] (1 : R))) = _
    rw [e.commutes (s ⊗ₜ[A] (1 : R)), IsScalarTower.algebraMap_apply T (S ⊗[A] L)
        (Localization.AtPrime 𝔮),
      algebraMap_tensor_tmul, map_one]
  · intro l
    suffices h : (e.toRingEquiv.toRingHom.comp φ) =
        (algebraMap (S ⊗[A] L) (Localization.AtPrime 𝔮)).comp
          (Algebra.TensorProduct.includeRight (R := A) (A := S) (B := L)).toRingHom by
      exact congrArg (fun f : L →+* Localization.AtPrime 𝔮 => f l) h
    refine IsLocalization.ringHom_ext 𝔭.primeCompl ?_
    ext r
    change e (φ (algebraMap R L r)) = algebraMap (S ⊗[A] L) (Localization.AtPrime 𝔮) ((1 : S)
        ⊗ₜ[A] algebraMap R L r)
    rw [hφ, ← algebraMap_tensor_tmul, ← IsScalarTower.algebraMap_apply]
    exact e.commutes ((1 : S) ⊗ₜ r)

end RightTensorLocalization

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

noncomputable section

/-- Reorder the tensor factors of a local presentation, preserving both coefficient maps. -/
lemma transport_tensor_localization {R A B C P : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing P]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (c : B ≃ₐ[R] C) (q : Ideal (C ⊗[R] A)) [q.IsPrime]
    (e : P ≃+* Localization.AtPrime q) (f : A →+* P) (g : B →+* P)
    (hf : ∀ a, e (f a) = algebraMap (C ⊗[R] A) (Localization.AtPrime q) ((1 : C) ⊗ₜ[R] a))
    (hg : ∀ b, e (g b) = algebraMap (C ⊗[R] A) (Localization.AtPrime q) (c b ⊗ₜ[R] (1 : A))) :
    ∃ (Q : Ideal (A ⊗[R] B)) (_ : Q.IsPrime) (e' : P ≃+* Localization.AtPrime Q),
      (∀ a, e' (f a) = algebraMap _ (Localization.AtPrime Q) (a ⊗ₜ[R] (1 : B))) ∧
      (∀ b, e' (g b) = algebraMap _ (Localization.AtPrime Q) ((1 : A) ⊗ₜ[R] b)) := by
  let ψ : A ⊗[R] B ≃ₐ[R] C ⊗[R] A :=
    (Algebra.TensorProduct.congr AlgEquiv.refl c).trans (Algebra.TensorProduct.comm R _ _)
  have hψ (a : A) (b : B) : ψ (a ⊗ₜ[R] b) = c b ⊗ₜ[R] a := by
    simp only [ψ, AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply,
      Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.comm_tmul]
    rfl
  let Q := q.comap ψ.toRingEquiv.toRingHom
  have hQ : Q.IsPrime := Ideal.comap_isPrime _ _
  have H : Q.primeCompl.map ψ.toRingEquiv.toMonoidHom = q.primeCompl := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      refine ⟨ψ.toRingEquiv.symm y, ?_, ψ.toRingEquiv.apply_symm_apply y⟩
      change ψ.toRingEquiv (ψ.toRingEquiv.symm y) ∉ q
      rw [ψ.toRingEquiv.apply_symm_apply]
      exact hy
  let ℓ : Localization.AtPrime Q ≃+* Localization.AtPrime q :=
    IsLocalization.ringEquivOfRingEquiv (M := Q.primeCompl) (T := q.primeCompl)
      (Localization.AtPrime Q) (Localization.AtPrime q) ψ.toRingEquiv H
  have hℓ (w : A ⊗[R] B) :
      ℓ (algebraMap _ (Localization.AtPrime Q) w) =
        algebraMap _ (Localization.AtPrime q) (ψ w) :=
    IsLocalization.ringEquivOfRingEquiv_eq H w
  clear_value Q ℓ ψ
  refine ⟨Q, hQ, e.trans ℓ.symm, fun a => ?_, fun b => ?_⟩
  · change ℓ.symm (e (f a)) = _
    rw [RingEquiv.symm_apply_eq, hf, hℓ, hψ, map_one]
  · change ℓ.symm (e (g b)) = _
    rw [RingEquiv.symm_apply_eq, hg, hℓ, hψ]

namespace AffineStalkCharts

variable {R : Type u} [CommRing R] {X Z : Scheme.{u}}
  (z : Z ⟶ Spec (CommRingCat.of R)) (f : X ⟶ Spec (CommRingCat.of R)) (U : Z.Opens) (hU :
      IsAffineOpen U)

lemma isoSpec_hom_sectionsAlgebra : letI := z.sectionsAlgebra U
    hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(Z, U))) = U.ι ≫ z := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec z (isAffineOpen_top _) hU (le_top : U ≤ z ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← IsAffineOpen.isoSpec_inv_ι] at h
  change hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ z.appLE ⊤ U le_top).hom) = _
  rw [CommRingCat.ofHom_hom, Spec.map_comp, h, Category.assoc, Iso.hom_inv_id_assoc]
omit U hU in
lemma algebraMap_stalk_eq {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of R)) (y : Y) [Algebra R
    (Y.presheaf.stalk y)]
    (halg : Y.fromSpecStalk y ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk
        y)))) (r : R) :
    algebraMap R (Y.presheaf.stalk y) r =
      Y.presheaf.germ ⊤ y trivial (g.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) := by
  have h1 : Y.fromSpecStalk y ≫ g ≫ (Spec (CommRingCat.of R)).toSpecΓ =
      Spec.map (g.appTop ≫ Y.presheaf.germ ⊤ y trivial) := by
    rw [Scheme.toSpecΓ_naturality, Scheme.fromSpecStalk_toSpecΓ_assoc, ← Spec.map_comp]
  rw [← Category.assoc, halg, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Spec.map_inj] at h1
  have h2 := congrArg (fun φ : Γ(Spec (CommRingCat.of R), ⊤) ⟶ Y.presheaf.stalk y =>
    φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) h1
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  erw [Iso.inv_hom_id_apply] at h2
  exact h2
omit U hU in
lemma fe_wrapper (k : Type u) [CommRing k] [Algebra R k] (g : Spec (CommRingCat.of k) ⟶ Spec
    (CommRingCat.of R))
    (hg : g = Spec.map (CommRingCat.ofHom (algebraMap R k)))
    (x : ↥(pullback f g))
    [inst : Algebra R (X.presheaf.stalk ((pullback.fst f g).base x))]
    (hinst : inst = ((X.presheaf.germ ⊤ ((pullback.fst f g).base x) trivial).hom.comp
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra) :
    ∃ (𝔮 : Ideal ((X.presheaf.stalk ((pullback.fst f g).base x)) ⊗[R] k)) (_ : 𝔮.IsPrime)
      (e : (pullback f g).presheaf.stalk x ≃+* Localization.AtPrime 𝔮),
      (∀ s : X.presheaf.stalk ((pullback.fst f g).base x),
        e (((pullback.fst f g).stalkMap x).hom s) =
          algebraMap ((X.presheaf.stalk ((pullback.fst f g).base x)) ⊗[R] k) (Localization.AtPrime
              𝔮) (s ⊗ₜ[R] 1)) ∧
      (∀ c : k,
        e ((pullback f g).presheaf.germ ⊤ x trivial ((pullback.snd f g).appTop ((Scheme.ΓSpecIso
            (CommRingCat.of k)).inv c))) =
          algebraMap ((X.presheaf.stalk ((pullback.fst f g).base x)) ⊗[R] k) (Localization.AtPrime
              𝔮) (1 ⊗ₜ[R] c)) := by
  subst hg hinst
  obtain ⟨𝔮, h𝔮, e, -, h1, h2⟩ :=
    AlgebraicGeometry.exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_of_germ_snd
        X f k x
  exact ⟨𝔮, h𝔮, e, h1, h2⟩

variable [Algebra R Γ(Z, U)]
  (hφU : hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(Z, U))) = U.ι ≫ z)

include hφU

/-- The structure morphism of the chosen affine chart. -/
def φ : Spec Γ(Z, U) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R Γ(Z,
    U)))

lemma fromSpec_φ : (hU.isoSpec.inv ≫ U.ι) ≫ z = φ (R := R) U := by
  rw [Category.assoc, ← hφU, Iso.inv_hom_id_assoc]; rfl

/-- The pullback map induced by the affine chart inclusion. -/
def jmap : pullback (φ (R := R) U) f ⟶ pullback z f :=
  pullback.map (φ (R := R) U) f z f (hU.isoSpec.inv ≫ U.ι) (𝟙 X) (𝟙 _)
    (by rw [Category.comp_id, fromSpec_φ z U hU hφU])
    (by rw [Category.comp_id, Category.id_comp])

/-- The same chart map after exchanging the two pullback factors. -/
def j : pullback f (φ (R := R) U) ⟶ pullback z f := (pullbackSymmetry f (φ (R := R) U)).hom ≫ jmap
    z f U hU hφU

local instance jmap_isOpenImmersion : IsOpenImmersion (jmap z f U hU hφU) := by
  unfold jmap
  infer_instance

local instance j_isOpenImmersion : IsOpenImmersion (j z f U hU hφU) := by
  unfold j
  infer_instance

lemma j_fst : j z f U hU hφU ≫ pullback.fst z f = pullback.snd f (φ (R := R) U) ≫ hU.isoSpec.inv ≫
    U.ι := by
  simp only [j, jmap, pullback.map, Category.assoc, pullback.lift_fst]
  rw [← Category.assoc, pullbackSymmetry_hom_comp_fst]

lemma j_snd : j z f U hU hφU ≫ pullback.snd z f = pullback.fst f (φ (R := R) U) := by
  simp only [j, jmap, pullback.map, Category.assoc, pullback.lift_snd, Category.comp_id]
  rw [pullbackSymmetry_hom_comp_snd]

lemma exists_j_eq (p : ↥(pullback z f)) (hpU : (pullback.fst z f).base p ∈ U) :
    ∃ q, (j z f U hU hφU).base q = p := by
  have : p ∈ Set.range (jmap z f U hU hφU).base := by
    unfold jmap
    rw [Scheme.Pullback.range_map]
    refine ⟨?_, ?_⟩
    · change (pullback.fst z f).base p ∈ Set.range (hU.isoSpec.inv ≫ U.ι).base
      rw [IsAffineOpen.isoSpec_inv_ι, IsAffineOpen.range_fromSpec]
      exact hpU
    · change (pullback.snd z f).base p ∈ Set.range (𝟙 X : X ⟶ X).base
      exact ⟨(pullback.snd z f).base p, rfl⟩
  obtain ⟨q', hq'⟩ := this
  refine ⟨(pullbackSymmetry f (φ (R := R) U)).inv.base q', ?_⟩
  unfold j
  change ((pullbackSymmetry f (φ (R := R) U)).inv ≫ (pullbackSymmetry f (φ (R := R) U)).hom ≫ jmap
      z f U hU hφU).base q' = p
  rw [Iso.inv_hom_id_assoc]
  exact hq'

/-- Germs of sections of the affine chart commute with the pullback chart map. -/
lemma chart_stalkMap_germ (q : ↥(pullback f (φ (R := R) U)))
    (hpU : (pullback.fst z f).base ((j z f U hU hφU).base q) ∈ U)
    (a : Γ(Z, U)) :
    (j z f U hU hφU).stalkMap q ((pullback z f).presheaf.germ
      ((pullback.fst z f) ⁻¹ᵁ U)
      ((j z f U hU hφU).base q) hpU ((pullback.fst z f).app U a)) =
      (pullback f (φ (R := R) U)).presheaf.germ ⊤ q trivial
        ((pullback.snd f (φ (R := R) U)).appTop ((Scheme.ΓSpecIso (CommRingCat.of Γ(Z, U))).inv
            a)) := by
  have hp : (j z f U hU hφU).base q ∈ (pullback.fst z f) ⁻¹ᵁ U := hpU
  refine ((j z f U hU hφU).germ_stalkMap_apply
    ((pullback.fst z f) ⁻¹ᵁ U) q hp ((pullback.fst z f).app U a)).trans ?_
  have hjf : (j z f U hU hφU) ≫ pullback.fst z f =
      pullback.snd f (φ (R := R) U) ≫ hU.fromSpec := by
    rw [j_fst, IsAffineOpen.isoSpec_inv_ι]
  have t := CategoryTheory.ConcreteCategory.congr_hom (Scheme.Hom.congr_app hjf U) a
  rw [Scheme.Hom.comp_app] at t
  erw [CommRingCat.comp_apply, CommRingCat.comp_apply] at t
  erw [t, TopCat.Presheaf.germ_res_apply]
  rw [Scheme.Hom.comp_app, IsAffineOpen.fromSpec_app_self]
  erw [CommRingCat.comp_apply, CommRingCat.comp_apply]
  have n := CategoryTheory.ConcreteCategory.congr_hom
    ((pullback.snd f (φ (R := R) U)).naturality (eqToHom hU.fromSpec_preimage_self).op)
    ((Scheme.ΓSpecIso Γ(Z, U)).inv a)
  erw [CommRingCat.comp_apply, CommRingCat.comp_apply] at n
  erw [n, TopCat.Presheaf.germ_res_apply]
  rfl

include hU in
theorem main
    (p : ↥(pullback z f))
    [Algebra R (Z.presheaf.stalk ((pullback.fst z f).base p))]
    (halgZ : Z.fromSpecStalk ((pullback.fst z f).base p) ≫ z =
      Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ((pullback.fst z f).base p)))))
    [Algebra R (X.presheaf.stalk ((pullback.snd z f).base p))]
    (halgX : X.fromSpecStalk ((pullback.snd z f).base p) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ((pullback.snd z f).base p)))))
    (hpU : (pullback.fst z f).base p ∈ U)
    (halgU : ∀ r : R, algebraMap R Γ(Z, U) r = (z.appLE ⊤ U le_top) ((Scheme.ΓSpecIso
        (CommRingCat.of R)).inv r)) :
    ∃ (𝔔 : Ideal ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk
        ((pullback.snd z f).base p))))
      (_ : 𝔔.IsPrime)
      (e : (pullback z f).presheaf.stalk p ≃+* Localization.AtPrime 𝔔),
      (∀ s : Z.presheaf.stalk ((pullback.fst z f).base p),
        e (((pullback.fst z f).stalkMap p).hom s) =
          algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk
              ((pullback.snd z f).base p)))
            (Localization.AtPrime 𝔔) (s ⊗ₜ[R] (1 : X.presheaf.stalk ((pullback.snd z f).base p)))) ∧
      (∀ t : X.presheaf.stalk ((pullback.snd z f).base p),
        e (((pullback.snd z f).stalkMap p).hom t) =
          algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk
              ((pullback.snd z f).base p)))
            (Localization.AtPrime 𝔔) ((1 : Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗ₜ[R] t))
                := by
  classical
  obtain ⟨q, rfl⟩ := exists_j_eq z f U hU hφU p hpU
  have hxx' : (pullback.snd z f).base ((j z f U hU hφU).base q) = (pullback.fst f (φ (R := R)
      U)).base q := by
    change ((j z f U hU hφU) ≫ pullback.snd z f).base q = _
    rw [j_snd z f U hU hφU]
  let aB' : Algebra R (X.presheaf.stalk ((pullback.fst f (φ (R := R) U)).base q)) :=
    ((X.presheaf.germ ⊤ ((pullback.fst f (φ (R := R) U)).base q) trivial).hom.comp
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
  let c : X.presheaf.stalk ((pullback.snd z f).base ((j z f U hU hφU).base q)) ≅ X.presheaf.stalk
      ((pullback.fst f (φ (R := R) U)).base q) := X.presheaf.stalkCongr (.of_eq hxx')
  have hc_germ : ∀ (W : X.Opens) (hW : (pullback.snd z f).base ((j z f U hU hφU).base q) ∈ W) (s :
      Γ(X, W)),
      c.hom (X.presheaf.germ W _ hW s) = X.presheaf.germ W ((pullback.fst f (φ (R := R) U)).base
          q) (hxx' ▸ hW) s := by
    intro W hW s
    change (X.presheaf.germ W _ hW ≫ X.presheaf.stalkSpecializes (specializes_of_eq hxx'.symm)) s
        = _
    rw [TopCat.Presheaf.germ_stalkSpecializes]
  have hc_alg : ∀ r : R, c.hom (algebraMap R (X.presheaf.stalk ((pullback.snd z f).base ((j z f U
      hU hφU).base q))) r) = algebraMap R (X.presheaf.stalk ((pullback.fst f (φ (R := R) U)).base
      q)) r := by
    intro r
    exact (congrArg c.hom (algebraMap_stalk_eq f _ halgX r)).trans
      (hc_germ ⊤ trivial (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)))
  let cA : X.presheaf.stalk ((pullback.snd z f).base ((j z f U hU hφU).base q)) ≃ₐ[R]
      X.presheaf.stalk ((pullback.fst f (φ (R := R) U)).base q) := AlgEquiv.ofRingEquiv (f :=
      c.commRingCatIsoToRingEquiv) hc_alg
  have E1 : ∀ t : X.presheaf.stalk ((pullback.snd z f).base ((j z f U hU hφU).base q)), (j z f U
      hU hφU).stalkMap q (((pullback.snd z f).stalkMap ((j z f U hU hφU).base q)).hom t) =
      ((pullback.fst f (φ (R := R) U)).stalkMap q).hom (c.hom t) := by
    intro t
    have h := Scheme.Hom.stalkMap_congr_hom ((j z f U hU hφU) ≫ pullback.snd z f) (pullback.fst f
        (φ (R := R) U)) (j_snd z f U hU hφU) q
    rw [Scheme.Hom.stalkMap_comp] at h
    exact CategoryTheory.ConcreteCategory.congr_hom h t
  have E2 : ∀ a : Γ(Z, U), (j z f U hU hφU).stalkMap q ((pullback z f).presheaf.germ
      ((pullback.fst z f) ⁻¹ᵁ U)
      ((j z f U hU hφU).base q) hpU ((pullback.fst z f).app U a)) =
      (pullback f (φ (R := R) U)).presheaf.germ ⊤ q trivial
        ((pullback.snd f (φ (R := R) U)).appTop ((Scheme.ΓSpecIso (CommRingCat.of Γ(Z, U))).inv
            a)) :=
    chart_stalkMap_germ z f U hU hφU q hpU
  have E1' : ∀ t, ((j z f U hU hφU).stalkMap q).hom (((pullback.snd z f).stalkMap ((j z f U hU
      hφU).base q)).hom t) =
      ((pullback.fst f (φ (R := R) U)).stalkMap q).hom (c.hom t) := fun t => E1 t
  have E2' : ∀ a : Γ(Z, U), ((j z f U hU hφU).stalkMap q).hom (((pullback.fst z f).stalkMap ((j z
      f U hU hφU).base q)).hom
      ((Z.presheaf.germ U _ hpU).hom a)) =
      (pullback f (φ (R := R) U)).presheaf.germ ⊤ q trivial
        ((pullback.snd f (φ (R := R) U)).appTop ((Scheme.ΓSpecIso (CommRingCat.of Γ(Z, U))).inv
            a)) := by
    intro a
    have g1 := CategoryTheory.ConcreteCategory.congr_hom
      (Scheme.Hom.germ_stalkMap (pullback.fst z f) U ((j z f U hU hφU).base q) hpU) a
    exact (congrArg (fun y => ((j z f U hU hφU).stalkMap q).hom y) g1).trans (E2 a)
  have few := fe_wrapper (R := R) f Γ(Z, U) (φ (R := R) U) rfl q (inst := aB') rfl
  obtain ⟨𝔮₀, h𝔮₀, e₀, he₀X, he₀A⟩ := few
  have : 𝔮₀.IsPrime := h𝔮₀
  let ζU : ↥U := ⟨(pullback.fst z f).base ((j z f U hU hφU).base q), hpU⟩
  let aZ : Algebra Γ(Z, U) (Z.presheaf.stalk ((pullback.fst z f).base ((j z f U hU hφU).base q))) :=
    (Z.presheaf.germ U _ hpU).hom.toAlgebra
  have hlocZ : IsLocalization.AtPrime (Z.presheaf.stalk ((pullback.fst z f).base ((j z f U hU
      hφU).base q)))
      (hU.primeIdealOf ζU).asIdeal := hU.isLocalization_stalk ζU
  have : IsScalarTower R Γ(Z, U) (Z.presheaf.stalk ((pullback.fst z f).base ((j z f U hU hφU).base
      q))) := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    rw [algebraMap_stalk_eq z _ halgZ r, halgU r]
    change _ = Z.presheaf.germ U _ hpU ((z.app ⊤ ≫ Z.presheaf.map (homOfLE le_top).op)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
    rw [CommRingCat.comp_apply]
    erw [TopCat.Presheaf.germ_res_apply]
    rfl
  let φL : Z.presheaf.stalk ((pullback.fst z f).base ((j z f U hU hφU).base q)) →+*
      Localization.AtPrime 𝔮₀ :=
    e₀.toRingHom.comp (((j z f U hU hφU).stalkMap q).hom.comp ((pullback.fst z f).stalkMap ((j z f
        U hU hφU).base q)).hom)
  have hφL : ∀ a : Γ(Z, U), φL (algebraMap Γ(Z, U) _ a) =
      algebraMap _ (Localization.AtPrime 𝔮₀)
        ((1 : X.presheaf.stalk ((pullback.fst f (φ (R := R) U)).base q)) ⊗ₜ[R] a) := by
    intro a
    exact (congrArg e₀ (E2' a)).trans (he₀A a)
  have hφLu : ∀ y, IsUnit (φL y) ↔ IsUnit y := by
    intro y
    have he : ∀ w, IsUnit (e₀ w) ↔ IsUnit w := fun w =>
      ⟨fun h => by simpa only [RingEquiv.symm_apply_apply] using h.map e₀.symm, fun h => h.map e₀⟩
    exact (he _).trans ((isUnit_map_iff ((j z f U hU hφU).stalkMap q).hom _).trans
      (isUnit_map_iff ((pullback.fst z f).stalkMap ((j z f U hU hφU).base q)).hom y))
  have hQp : 𝔮₀.comap (Algebra.TensorProduct.includeRight (R := R)
      (A := X.presheaf.stalk ((pullback.fst f (φ (R := R) U)).base q)) (B := Γ(Z, U))).toRingHom =
          (hU.primeIdealOf ζU).asIdeal := by
    ext a
    rw [Ideal.mem_comap]
    change ((1 : X.presheaf.stalk ((pullback.fst f (φ (R := R) U)).base q)) ⊗ₜ[R] a ∈ 𝔮₀) ↔ a ∈
        (hU.primeIdealOf ζU).asIdeal
    have h1 : ((1 : X.presheaf.stalk ((pullback.fst f (φ (R := R) U)).base q)) ⊗ₜ[R] a ∈ 𝔮₀) ↔
        ¬ IsUnit (algebraMap _ (Localization.AtPrime 𝔮₀) ((1 : X.presheaf.stalk ((pullback.fst f
            (φ (R := R) U)).base q)) ⊗ₜ[R] a)) := by
      rw [IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime 𝔮₀) 𝔮₀]
      exact not_not.symm
    have h2 : a ∈ (hU.primeIdealOf ζU).asIdeal ↔
        ¬ IsUnit (algebraMap Γ(Z, U) (Z.presheaf.stalk ((pullback.fst z f).base ((j z f U hU
            hφU).base q))) a) := by
      rw [IsLocalization.AtPrime.isUnit_to_map_iff _ (hU.primeIdealOf ζU).asIdeal]
      exact not_not.symm
    rw [h1, h2, ← hφL a, not_iff_not]
    exact hφLu _
  have cr := RightTensorLocalization.core (A := R)
    (S := X.presheaf.stalk ((pullback.fst f (φ (R := R) U)).base q)) (R := Γ(Z, U))
    (L := Z.presheaf.stalk ((pullback.fst z f).base ((j z f U hU hφU).base q)))
    (hU.primeIdealOf ζU).asIdeal 𝔮₀ hQp (Localization.AtPrime 𝔮₀) φL hφL
  obtain ⟨𝔮₁, h𝔮₁, e₁, he₁S, he₁L⟩ := cr
  have : 𝔮₁.IsPrime := h𝔮₁
  have hφL_def : ∀ s, φL s = e₀ (((j z f U hU hφU).stalkMap q).hom
      (((pullback.fst z f).stalkMap ((j z f U hU hφU).base q)).hom s)) := fun s => rfl
  clear_value φL
  have : IsIso ((j z f U hU hφU).stalkMap q) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 q
  let eJ := (asIso ((j z f U hU hφU).stalkMap q)).commRingCatIsoToRingEquiv
  have heJ (w : (pullback z f).presheaf.stalk ((j z f U hU hφU).base q)) :
      eJ w = ((j z f U hU hφU).stalkMap q).hom w := rfl
  clear_value eJ
  apply transport_tensor_localization cA 𝔮₁ (eJ.trans (e₀.trans e₁))
    (((pullback.fst z f).stalkMap ((j z f U hU hφU).base q)).hom)
    (((pullback.snd z f).stalkMap ((j z f U hU hφU).base q)).hom)
  · intro s
    exact (congrArg (fun w => e₁ (e₀ w)) (heJ _)).trans
      ((congrArg e₁ (hφL_def s).symm).trans (he₁L s))
  · intro t
    exact (congrArg (fun w => e₁ (e₀ w)) (heJ _)).trans
      ((congrArg (fun w => e₁ (e₀ w)) (E1' t)).trans
        ((congrArg e₁ (he₀X (c.hom t))).trans (he₁S (c.hom t))))

end AffineStalkCharts

end

theorem
    _root_.AlgebraicGeometry.exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_stalk
    {R : Type u} [CommRing R] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (z : Z ⟶ Spec (CommRingCat.of R))
    (p : ↥(pullback z f))
    [Algebra R (Z.presheaf.stalk ((pullback.fst z f).base p))]
    (halgZ : Z.fromSpecStalk ((pullback.fst z f).base p) ≫ z =
      Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ((pullback.fst z f).base p)))))
    [Algebra R (X.presheaf.stalk ((pullback.snd z f).base p))]
    (halgX : X.fromSpecStalk ((pullback.snd z f).base p) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ((pullback.snd z f).base p))))) :
    ∃ (𝔔 : Ideal ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk
        ((pullback.snd z f).base p))))
      (_ : 𝔔.IsPrime)
      (e : (pullback z f).presheaf.stalk p ≃+* Localization.AtPrime 𝔔),
      (∀ s : Z.presheaf.stalk ((pullback.fst z f).base p),
        e (((pullback.fst z f).stalkMap p).hom s) =
          algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk
              ((pullback.snd z f).base p)))
            (Localization.AtPrime 𝔔) (s ⊗ₜ[R] (1 : X.presheaf.stalk ((pullback.snd z f).base p)))) ∧
      (∀ t : X.presheaf.stalk ((pullback.snd z f).base p),
        e (((pullback.snd z f).stalkMap p).hom t) =
          algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk
              ((pullback.snd z f).base p)))
            (Localization.AtPrime 𝔔) ((1 : Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗ₜ[R] t))
                := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ ((pullback.fst z f).base p))
        isOpen_univ
  let : Algebra R Γ(Z, U) := z.sectionsAlgebra U
  exact AffineStalkCharts.main z f U hU (AffineStalkCharts.isoSpec_hom_sectionsAlgebra z U hU) p
      halgZ halgX hpU (fun r => rfl)

end AbelianVarieties.NOSProofs.StalkPullbackLocalizations

end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_maximalIdeal_stalk_pullback_eq_map_stalkMap_fst_sup_map_stalkMap_snd_of_section.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.SectionStalkIdeals

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

/-- The unique point of the spectrum of a field, with its scheme carrier type. -/
noncomputable def fieldPoint (k : Type u) [Field k] : ↥(Spec (CommRingCat.of k)) :=
  IsLocalRing.closedPoint k

namespace AffineModel

lemma map_maximalIdeal_of_iso {R S : CommRingCat.{u}} [IsLocalRing R] [IsLocalRing S]
    (e : R ≅ S) :
    (IsLocalRing.maximalIdeal R).map e.hom.hom = IsLocalRing.maximalIdeal S :=
  IsLocalRing.map_maximalIdeal_of_surjective e.hom.hom
    e.commRingCatIsoToRingEquiv.surjective

lemma map_stalk_eq {R₁ S₁ R₂ S₂ : CommRingCat.{u}} [IsLocalRing R₁] [IsLocalRing R₂]
    (u : R₁ ⟶ S₁) (v : R₂ ⟶ S₂) (eL : R₁ ≅ R₂) (eR : S₁ ≅ S₂) (h : eL.hom ≫ v ≫ eR.inv = u) :
    (IsLocalRing.maximalIdeal R₁).map u.hom =
      ((IsLocalRing.maximalIdeal R₂).map v.hom).map eR.inv.hom := by
  rw [← h, CommRingCat.hom_comp, CommRingCat.hom_comp, ← Ideal.map_map, ← Ideal.map_map,
    map_maximalIdeal_of_iso eL]

/-- A sum of extended ideals localizes to the corresponding sum of maximal ideals. -/
lemma maximalIdeal_localization_of_sup {A B T : CommRingCat.{u}}
    (f₁ : A ⟶ T) (f₂ : B ⟶ T) (q : PrimeSpectrum T)
    (hq : q.asIdeal = (q.comap f₁.hom).asIdeal.map f₁.hom ⊔
      (q.comap f₂.hom).asIdeal.map f₂.hom) :
    IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) =
      (IsLocalRing.maximalIdeal (Localization.AtPrime (q.comap f₁.hom).asIdeal)).map
        (Localization.localRingHom (q.comap f₁.hom).asIdeal q.asIdeal f₁.hom rfl) ⊔
      (IsLocalRing.maximalIdeal (Localization.AtPrime (q.comap f₂.hom).asIdeal)).map
        (Localization.localRingHom (q.comap f₂.hom).asIdeal q.asIdeal f₂.hom rfl) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Localization.AtPrime.map_eq_maximalIdeal,
    ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_map]
  erw [IsLocalization.map_comp, IsLocalization.map_comp]
  rw [← Ideal.map_map, ← Ideal.map_map, ← Ideal.map_sup, ← hq]

/-- Identify a maximal-ideal sum on affine stalks from the same sum in their coordinate ring. -/
lemma maximalIdeal_stalk_of_sup {A B T : CommRingCat.{u}}
    (f₁ : A ⟶ T) (f₂ : B ⟶ T) (q : ↥(Spec T))
    (hq : q.asIdeal = (q.comap f₁.hom).asIdeal.map f₁.hom ⊔
      (q.comap f₂.hom).asIdeal.map f₂.hom) :
    IsLocalRing.maximalIdeal ((Spec T).presheaf.stalk q) =
      (IsLocalRing.maximalIdeal ((Spec A).presheaf.stalk ((Spec.map f₁) q))).map
        ((Spec.map f₁).stalkMap q).hom ⊔
      (IsLocalRing.maximalIdeal ((Spec B).presheaf.stalk ((Spec.map f₂) q))).map
        ((Spec.map f₂).stalkMap q).hom := by
  have hprime : q.asIdeal.IsPrime := (q : PrimeSpectrum T).isPrime
  have hlocalA : IsLocalRing ((Spec A).presheaf.stalk (q.comap f₁.hom)) :=
    (Spec A).toLocallyRingedSpace.isLocalRing ((Spec.map f₁) q)
  have hlocalB : IsLocalRing ((Spec B).presheaf.stalk (q.comap f₂.hom)) :=
    (Spec B).toLocallyRingedSpace.isLocalRing ((Spec.map f₂) q)
  have h₁ := Scheme.localRingHom_comp_stalkIso f₁ q
  have h₂ := Scheme.localRingHom_comp_stalkIso f₂ q
  have hT : IsLocalRing.maximalIdeal ((Spec T).presheaf.stalk q) =
      (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)).map
        (Spec.stalkIso T q).inv.hom :=
    (map_maximalIdeal_of_iso (Spec.stalkIso T q).symm).symm
  refine hT.trans ?_
  rw [maximalIdeal_localization_of_sup f₁ f₂ q hq, Ideal.map_sup]
  exact congrArg₂ (· ⊔ ·) (map_stalk_eq _ _ _ _ h₁).symm
    (map_stalk_eq _ _ _ _ h₂).symm

/-- A commuting triangle transports the image of the maximal ideal without unfolding stalks. -/
lemma map_maximalIdeal_comp_of_eq {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hfg : f ≫ g = h) (x : X) :
    (IsLocalRing.maximalIdeal (Z.presheaf.stalk (g (f x)))).map
      (g.stalkMap (f x) ≫ f.stalkMap x).hom =
    (IsLocalRing.maximalIdeal (Z.presheaf.stalk (h x))).map (h.stalkMap x).hom := by
  subst h
  exact congrArg (fun m : Z.presheaf.stalk (g (f x)) ⟶ X.presheaf.stalk x =>
    (IsLocalRing.maximalIdeal (Z.presheaf.stalk (g (f x)))).map m.hom)
      (Scheme.Hom.stalkMap_comp f g x).symm

/-- An isomorphism on the intermediate stalk removes its maximal-ideal image from a composite. -/
lemma map_maximalIdeal_comp_of_isIso {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) [IsIso (g.stalkMap (f x))] :
    (IsLocalRing.maximalIdeal (Z.presheaf.stalk ((f ≫ g) x))).map
      ((f ≫ g).stalkMap x).hom =
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom := by
  refine (map_maximalIdeal_comp_of_eq f g (f ≫ g) rfl x).symm.trans ?_
  change (IsLocalRing.maximalIdeal (Z.presheaf.stalk (g (f x)))).map
    ((f.stalkMap x).hom.comp (g.stalkMap (f x)).hom) = _
  rw [← Ideal.map_map]
  exact congrArg (Ideal.map (f.stalkMap x).hom)
    (map_maximalIdeal_of_iso (asIso (g.stalkMap (f x))))

variable {k : Type u} [Field k] {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  (εA : A →ₐ[k] k) (εB : B →ₐ[k] k)

/-- The augmentation on a tensor product determined by the two sections. -/
noncomputable def ε : A ⊗[k] B →ₐ[k] k :=
  Algebra.TensorProduct.lift εA εB (fun _ _ ↦ Commute.all _ _)

lemma εA_surjective : Function.Surjective εA := fun c ↦ ⟨algebraMap k A c, εA.commutes c⟩

lemma εB_surjective : Function.Surjective εB := fun c ↦ ⟨algebraMap k B c, εB.commutes c⟩

lemma ε_eq_comp : (ε εA εB : A ⊗[k] B →ₐ[k] k) =
    (Algebra.TensorProduct.lmul' k (S := k)).comp (Algebra.TensorProduct.map εA εB) := by
  apply Algebra.TensorProduct.ext'
  intro a b
  simp only [ε, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lmul'_apply_tmul]

theorem ker_ε :
    RingHom.ker (ε εA εB : A ⊗[k] B →ₐ[k] k) =
      (RingHom.ker εA).map (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B) ⊔
        (RingHom.ker εB).map (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B) := by
  rw [← Algebra.TensorProduct.map_ker εA εB (εA_surjective εA) (εB_surjective εB)]
  ext t
  simp only [RingHom.mem_ker]
  rw [ε_eq_comp]
  change Algebra.TensorProduct.lmul' k (Algebra.TensorProduct.map εA εB t) = 0 ↔ _
  constructor
  · intro h
    have key : ∀ w : k ⊗[k] k, Algebra.TensorProduct.lmul' k (S := k) w =
        Algebra.TensorProduct.lid k k w := by
      intro w
      induction w using TensorProduct.inductionOn with
      | tmul a b =>
        simp only [Algebra.TensorProduct.lmul'_apply_tmul, Algebra.TensorProduct.lid_tmul,
          Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply]
      | add u v hu hv => simp only [map_add, hu, hv]
    have hinj : Function.Injective (Algebra.TensorProduct.lmul' k (S := k) : k ⊗[k] k → k) := by
      intro u v huv
      rw [key, key] at huv
      exact (Algebra.TensorProduct.lid k k).injective huv
    exact hinj (by rw [h, map_zero])
  · intro h
    change (Algebra.TensorProduct.map εA εB) t = 0 at h
    rw [h, map_zero]

local instance isMaximal_ker_ε : (RingHom.ker (ε εA εB : A ⊗[k] B →ₐ[k] k)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun c ↦ ⟨algebraMap k _ c, AlgHom.commutes _ c⟩

/-- The point of the tensor-product spectrum defined by the common augmentation. -/
noncomputable def qpt : ↥(Spec (CommRingCat.of (A ⊗[k] B))) :=
  (⟨RingHom.ker (ε εA εB : A ⊗[k] B →ₐ[k] k), inferInstance⟩ :
    PrimeSpectrum (A ⊗[k] B))

lemma comap_includeLeft_ker :
    (RingHom.ker (ε εA εB : A ⊗[k] B →ₐ[k] k)).comap
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[k] B) = RingHom.ker εA := by
  ext a
  change ε εA εB (a ⊗ₜ[k] 1) = 0 ↔ εA a = 0
  rw [ε, Algebra.TensorProduct.lift_tmul, map_one, mul_one]

lemma comap_includeRight_ker :
    (RingHom.ker (ε εA εB : A ⊗[k] B →ₐ[k] k)).comap
      ((Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B).toRingHom) = RingHom.ker εB := by
  ext b
  change ε εA εB (1 ⊗ₜ[k] b) = 0 ↔ εB b = 0
  rw [ε, Algebra.TensorProduct.lift_tmul, map_one, one_mul]

/-- The first projection from the affine tensor-product model. -/
noncomputable abbrev p₁ : Spec (CommRingCat.of (A ⊗[k] B)) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[k] B))

/-- The second projection from the affine tensor-product model. -/
noncomputable abbrev p₂ : Spec (CommRingCat.of (A ⊗[k] B)) ⟶ Spec (CommRingCat.of B) :=
  Spec.map (CommRingCat.ofHom (R := B) (S := A ⊗[k] B)
    (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B).toRingHom)

theorem maximalIdeal_stalk_eq :
    IsLocalRing.maximalIdeal ((Spec (CommRingCat.of (A ⊗[k] B))).presheaf.stalk (qpt εA εB)) =
      (IsLocalRing.maximalIdeal ((Spec (CommRingCat.of A)).presheaf.stalk (p₁ (k := k) (A := A) (B
          := B)
          (qpt εA εB)))).map ((p₁ (k := k) (A := A) (B := B)).stalkMap (qpt εA εB)).hom ⊔
      (IsLocalRing.maximalIdeal ((Spec (CommRingCat.of B)).presheaf.stalk (p₂ (k := k) (A := A) (B
          := B)
          (qpt εA εB)))).map ((p₂ (k := k) (A := A) (B := B)).stalkMap (qpt εA εB)).hom := by
  apply maximalIdeal_stalk_of_sup
    (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[k] B))
    (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B).toRingHom)
    (qpt εA εB)
  change RingHom.ker (ε εA εB : A ⊗[k] B →ₐ[k] k) =
    ((RingHom.ker (ε εA εB : A ⊗[k] B →ₐ[k] k)).comap
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[k] B)).map _ ⊔
    ((RingHom.ker (ε εA εB : A ⊗[k] B →ₐ[k] k)).comap
      (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B).toRingHom).map _
  rw [comap_includeLeft_ker, comap_includeRight_ker]
  exact ker_ε εA εB

end AffineModel

namespace AffineModel

open CategoryTheory.Limits

variable {k : Type u} [Field k] {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  (εA : A →ₐ[k] k) (εB : B →ₐ[k] k)

lemma transport {P₀ S₀ X₁ X₂ : CommRingCat.{u}} [IsLocalRing P₀] [IsLocalRing S₀] [IsLocalRing X₁]
    [IsLocalRing X₂] (θ : P₀ ⟶ S₀) [IsIso θ] (u₁ : X₁ ⟶ P₀) (u₂ : X₂ ⟶ P₀)
    (h : IsLocalRing.maximalIdeal S₀ = (IsLocalRing.maximalIdeal X₁).map (u₁ ≫ θ).hom ⊔
        (IsLocalRing.maximalIdeal X₂).map (u₂ ≫ θ).hom) :
    IsLocalRing.maximalIdeal P₀ =
      (IsLocalRing.maximalIdeal X₁).map u₁.hom ⊔ (IsLocalRing.maximalIdeal X₂).map u₂.hom := by
  have hbij : Function.Bijective θ.hom := (asIso θ).commRingCatIsoToRingEquiv.bijective
  have hθ : (IsLocalRing.maximalIdeal P₀).map θ.hom = IsLocalRing.maximalIdeal S₀ :=
    map_maximalIdeal_of_iso (asIso θ)
  apply_fun Ideal.comap θ.hom at hθ
  rw [Ideal.comap_map_of_bijective _ hbij] at hθ
  rw [hθ, h, CommRingCat.hom_comp, CommRingCat.hom_comp, ← Ideal.map_map, ← Ideal.map_map,
    ← Ideal.map_sup, Ideal.comap_map_of_bijective _ hbij]

theorem spec_case
    (hx : Spec.map (CommRingCat.ofHom εA.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k A)) = 𝟙 _)
    (hy : Spec.map (CommRingCat.ofHom εB.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k B)) = 𝟙 _) :
    IsLocalRing.maximalIdeal ((pullback (Spec.map (CommRingCat.ofHom (algebraMap k A)))
        (Spec.map (CommRingCat.ofHom (algebraMap k B)))).presheaf.stalk
        (pullback.lift (Spec.map (CommRingCat.ofHom εA.toRingHom))
          (Spec.map (CommRingCat.ofHom εB.toRingHom)) (hx.trans hy.symm) (fieldPoint k))) =
      (IsLocalRing.maximalIdeal ((Spec (CommRingCat.of A)).presheaf.stalk
          (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A)))
            (Spec.map (CommRingCat.ofHom (algebraMap k B)))
            (pullback.lift (Spec.map (CommRingCat.ofHom εA.toRingHom))
              (Spec.map (CommRingCat.ofHom εB.toRingHom)) (hx.trans hy.symm)
                (fieldPoint k))))).map
        ((pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A)))
            (Spec.map (CommRingCat.ofHom (algebraMap k B)))).stalkMap
          (pullback.lift (Spec.map (CommRingCat.ofHom εA.toRingHom))
            (Spec.map (CommRingCat.ofHom εB.toRingHom)) (hx.trans hy.symm)
              (fieldPoint k))).hom ⊔
      (IsLocalRing.maximalIdeal ((Spec (CommRingCat.of B)).presheaf.stalk
          (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A)))
            (Spec.map (CommRingCat.ofHom (algebraMap k B)))
            (pullback.lift (Spec.map (CommRingCat.ofHom εA.toRingHom))
              (Spec.map (CommRingCat.ofHom εB.toRingHom)) (hx.trans hy.symm)
                (fieldPoint k))))).map
        ((pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A)))
            (Spec.map (CommRingCat.ofHom (algebraMap k B)))).stalkMap
          (pullback.lift (Spec.map (CommRingCat.ofHom εA.toRingHom))
            (Spec.map (CommRingCat.ofHom εB.toRingHom)) (hx.trans hy.symm)
              (fieldPoint k))).hom := by
  set fX := Spec.map (CommRingCat.ofHom (algebraMap k A)) with hfX
  set fY := Spec.map (CommRingCat.ofHom (algebraMap k B)) with hfY
  set x := Spec.map (CommRingCat.ofHom εA.toRingHom) with hxdef
  set y := Spec.map (CommRingCat.ofHom εB.toRingHom) with hydef
  let ι : Spec (CommRingCat.of (A ⊗[k] B)) ⟶ pullback fX fY := (pullbackSpecIso k A B).inv
  let σ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (A ⊗[k] B)) :=
    Spec.map (CommRingCat.ofHom (ε εA εB : A ⊗[k] B →ₐ[k] k).toRingHom)
  have hι₁ : ι ≫ pullback.fst fX fY = p₁ (k := k) (A := A) (B := B) := pullbackSpecIso_inv_fst k A B
  have hι₂ : ι ≫ pullback.snd fX fY = p₂ (k := k) (A := A) (B := B) := pullbackSpecIso_inv_snd k A B
  have hσ₁ : σ ≫ p₁ (k := k) (A := A) (B := B) = x := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext a
    change (ε εA εB) (a ⊗ₜ 1) = εA a
    rw [ε, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  have hσ₂ : σ ≫ p₂ (k := k) (A := A) (B := B) = y := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext b
    change (ε εA εB) (1 ⊗ₜ b) = εB b
    rw [ε, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  have hσι : σ ≫ ι = pullback.lift x y (hx.trans hy.symm) := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, hι₁, hσ₁]
    · rw [pullback.lift_snd, Category.assoc, hι₂, hσ₂]
  have hσpt : σ (fieldPoint k) = qpt εA εB := by
    apply PrimeSpectrum.ext
    change Ideal.comap (ε εA εB : A ⊗[k] B →ₐ[k] k).toRingHom
      (IsLocalRing.maximalIdeal k) = _
    rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp (Field.toIsField k),
      ← RingHom.ker_eq_comap_bot]
    rfl
  have hz : pullback.lift x y (hx.trans hy.symm) (fieldPoint k) = ι (qpt εA εB) := by
    rw [← hσι, Scheme.Hom.comp_apply, hσpt]
  generalize pullback.lift x y (hx.trans hy.symm) (fieldPoint k) = z at hz ⊢
  subst hz
  refine transport (ι.stalkMap (qpt εA εB)) _ _ ?_
  exact (maximalIdeal_stalk_eq εA εB).trans (congrArg₂ (· ⊔ ·)
    (map_maximalIdeal_comp_of_eq ι (pullback.fst fX fY) _ hι₁ (qpt εA εB)).symm
    (map_maximalIdeal_comp_of_eq ι (pullback.snd fX fY) _ hι₂ (qpt εA εB)).symm)

end AffineModel

namespace AffineDescent

open CategoryTheory.Limits AffineModel

theorem main {k : Type u} [Field k] {X Y : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    (x : Spec (CommRingCat.of k) ⟶ X) (hx : x ≫ fX = 𝟙 _)
    (y : Spec (CommRingCat.of k) ⟶ Y) (hy : y ≫ fY = 𝟙 _) :
    IsLocalRing.maximalIdeal ((pullback fX fY).presheaf.stalk
        (pullback.lift x y (hx.trans hy.symm) (fieldPoint k))) =
      (IsLocalRing.maximalIdeal (X.presheaf.stalk
          (pullback.fst fX fY (pullback.lift x y (hx.trans hy.symm) (fieldPoint k))))).map
        ((pullback.fst fX fY).stalkMap
          (pullback.lift x y (hx.trans hy.symm) (fieldPoint k))).hom ⊔
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk
          (pullback.snd fX fY (pullback.lift x y (hx.trans hy.symm) (fieldPoint k))))).map
        ((pullback.snd fX fY).stalkMap
          (pullback.lift x y (hx.trans hy.symm) (fieldPoint k))).hom := by
  obtain ⟨_, ⟨U', hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (x (fieldPoint k)))
      isOpen_univ
  obtain ⟨_, ⟨V', hV, rfl⟩, hyV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (y (fieldPoint k)))
      isOpen_univ
  let U : X.Opens := U'
  let V : Y.Opens := V'
  replace hU : IsAffineOpen U := hU
  replace hV : IsAffineOpen V := hV
  replace hxU : x (fieldPoint k) ∈ U := hxU
  replace hyV : y (fieldPoint k) ∈ V := hyV
  let iU : Spec Γ(X, U) ⟶ X := hU.isoSpec.inv ≫ U.ι
  let iV : Spec Γ(Y, V) ⟶ Y := hV.isoSpec.inv ≫ V.ι
  have : IsOpenImmersion iU := IsOpenImmersion.comp _ _
  have : IsOpenImmersion iV := IsOpenImmersion.comp _ _
  obtain ⟨ψA, hψA⟩ := Spec.map_surjective (iU ≫ fX)
  obtain ⟨ψB, hψB⟩ := Spec.map_surjective (iV ≫ fY)
  have hxr : Set.range x ⊆ Set.range iU := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : fieldPoint k = p := Subsingleton.elim _ _
    have : Set.range iU = (U : Set X) := by
      change Set.range (hU.isoSpec.inv ≫ U.ι) = _
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Set.range_eq_univ.mpr hU.isoSpec.inv.surjective, Set.image_univ,
        Scheme.Opens.range_ι]
    rw [this]; exact hxU
  have hyr : Set.range y ⊆ Set.range iV := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : fieldPoint k = p := Subsingleton.elim _ _
    have : Set.range iV = (V : Set Y) := by
      change Set.range (hV.isoSpec.inv ≫ V.ι) = _
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Set.range_eq_univ.mpr hV.isoSpec.inv.surjective, Set.image_univ,
        Scheme.Opens.range_ι]
    rw [this]; exact hyV
  let x' : Spec (CommRingCat.of k) ⟶ Spec Γ(X, U) := IsOpenImmersion.lift iU x hxr
  let y' : Spec (CommRingCat.of k) ⟶ Spec Γ(Y, V) := IsOpenImmersion.lift iV y hyr
  have hx' : x' ≫ iU = x := IsOpenImmersion.lift_fac _ _ _
  have hy' : y' ≫ iV = y := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨χA, hχA⟩ := Spec.map_surjective x'
  obtain ⟨χB, hχB⟩ := Spec.map_surjective y'
  have hψχA : ψA ≫ χA = 𝟙 _ := by
    rw [← Spec.map_eq_id, Spec.map_comp, hχA, hψA, ← Category.assoc, hx', hx]
  have hψχB : ψB ≫ χB = 𝟙 _ := by
    rw [← Spec.map_eq_id, Spec.map_comp, hχB, hψB, ← Category.assoc, hy', hy]
  let : Algebra k Γ(X, U) := ψA.hom.toAlgebra
  let : Algebra k Γ(Y, V) := ψB.hom.toAlgebra
  let εA : Γ(X, U) →ₐ[k] k :=
    { χA.hom with
      commutes' := fun c ↦ by
        change χA.hom (ψA.hom c) = c
        rw [← CommRingCat.comp_apply, hψχA]; rfl }
  let εB : Γ(Y, V) →ₐ[k] k :=
    { χB.hom with
      commutes' := fun c ↦ by
        change χB.hom (ψB.hom c) = c
        rw [← CommRingCat.comp_apply, hψχB]; rfl }
  let fX₀ := Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U)))
  let fY₀ := Spec.map (CommRingCat.ofHom (algebraMap k Γ(Y, V)))
  let x₀ := Spec.map (CommRingCat.ofHom εA.toRingHom)
  let y₀ := Spec.map (CommRingCat.ofHom εB.toRingHom)
  have hψA' : fX₀ = iU ≫ fX := hψA
  have hψB' : fY₀ = iV ≫ fY := hψB
  have hχA' : x₀ = x' := hχA
  have hχB' : y₀ = y' := hχB
  have hx₀ : x₀ ≫ fX₀ = 𝟙 _ := by
    rw [hχA', hψA', ← Category.assoc, hx', hx]
  have hy₀ : y₀ ≫ fY₀ = 𝟙 _ := by
    rw [hχB', hψB', ← Category.assoc, hy', hy]
  have haff := spec_case εA εB hx₀ hy₀
  let j : pullback fX₀ fY₀ ⟶ pullback fX fY :=
    pullback.map fX₀ fY₀ fX fY iU iV (𝟙 _) ((Category.comp_id _).trans hψA')
      ((Category.comp_id _).trans hψB')
  have : IsOpenImmersion j := Scheme.pullback_map_isOpenImmersion _ _ _ _ _ _ _ _ _
  have hj₁ : j ≫ pullback.fst fX fY = pullback.fst fX₀ fY₀ ≫ iU := pullback.lift_fst _ _ _
  have hj₂ : j ≫ pullback.snd fX fY = pullback.snd fX₀ fY₀ ≫ iV := pullback.lift_snd _ _ _
  have hz : pullback.lift x y (hx.trans hy.symm) = pullback.lift x₀ y₀ (hx₀.trans hy₀.symm) ≫ j :=
      by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, hj₁, pullback.lift_fst_assoc, hχA', hx']
    · rw [pullback.lift_snd, Category.assoc, hj₂, pullback.lift_snd_assoc, hχB', hy']
  have hzpt : pullback.lift x y (hx.trans hy.symm) (fieldPoint k) =
      j (pullback.lift x₀ y₀ (hx₀.trans hy₀.symm) (fieldPoint k)) := by
    rw [hz, Scheme.Hom.comp_apply]
  generalize pullback.lift x y (hx.trans hy.symm) (fieldPoint k) = z at hzpt ⊢
  subst hzpt
  let z₀ := pullback.lift x₀ y₀ (hx₀.trans hy₀.symm) (fieldPoint k)
  refine transport (j.stalkMap z₀) _ _ ?_
  have h₁ := (map_maximalIdeal_comp_of_eq j (pullback.fst fX fY) _ hj₁ z₀).trans
    (map_maximalIdeal_comp_of_isIso (pullback.fst fX₀ fY₀) iU z₀)
  have h₂ := (map_maximalIdeal_comp_of_eq j (pullback.snd fX fY) _ hj₂ z₀).trans
    (map_maximalIdeal_comp_of_isIso (pullback.snd fX₀ fY₀) iV z₀)
  exact haff.trans (congrArg₂ (· ⊔ ·) h₁.symm h₂.symm)

end AffineDescent

end AbelianVarieties.NOSProofs.SectionStalkIdeals

namespace AlgebraicGeometry

universe u

open CategoryTheory CategoryTheory.Limits

theorem maximalIdeal_stalk_pullback_eq_map_stalkMap_fst_sup_map_stalkMap_snd_of_section
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    (x : Spec (CommRingCat.of k) ⟶ X) (hx : x ≫ fX = 𝟙 _)
    (y : Spec (CommRingCat.of k) ⟶ Y) (hy : y ≫ fY = 𝟙 _) :
    IsLocalRing.maximalIdeal ((Limits.pullback fX fY).presheaf.stalk
        (Limits.pullback.lift x y (hx.trans hy.symm) (IsLocalRing.closedPoint k))) =
      (IsLocalRing.maximalIdeal (X.presheaf.stalk
          (Limits.pullback.fst fX fY (Limits.pullback.lift x y (hx.trans hy.symm)
            (IsLocalRing.closedPoint k))))).map
        ((Limits.pullback.fst fX fY).stalkMap
          (Limits.pullback.lift x y (hx.trans hy.symm) (IsLocalRing.closedPoint k))).hom ⊔
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk
          (Limits.pullback.snd fX fY (Limits.pullback.lift x y (hx.trans hy.symm)
            (IsLocalRing.closedPoint k))))).map
        ((Limits.pullback.snd fX fY).stalkMap
          (Limits.pullback.lift x y (hx.trans hy.symm) (IsLocalRing.closedPoint k))).hom :=
  AbelianVarieties.NOSProofs.SectionStalkIdeals.AffineDescent.main fX fY x hx y hy

end AlgebraicGeometry

end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_maximalIdeal_stalk_pullback_le_of_sections_of_isAffine.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

theorem _root_.AlgebraicGeometry.maximalIdeal_stalk_pullback_le_of_sections_of_isAffine
    {k : Type u} [Field k] {Y Z : Scheme.{u}} [IsAffine Y] [IsAffine Z]
    (pY : Y ⟶ Spec (.of k)) (pZ : Z ⟶ Spec (.of k))
    (y : Spec (.of k) ⟶ Y) (hy : y ≫ pY = 𝟙 _) (z : Spec (.of k) ⟶ Z) (hz : z ≫ pZ = 𝟙 _)
    (w : ↑(pullback pY pZ)) (hw : w = (pullback.lift y z (hy.trans hz.symm)) (closedPoint k)) :
    maximalIdeal ((pullback pY pZ).presheaf.stalk w) ≤
      (maximalIdeal _).map ((pullback.fst pY pZ).stalkMap w).hom ⊔
        (maximalIdeal _).map ((pullback.snd pY pZ).stalkMap w).hom := by
  subst hw
  exact (maximalIdeal_stalk_pullback_eq_map_stalkMap_fst_sup_map_stalkMap_snd_of_section
    pY pZ y hy z hz).le

end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_bijective_kaehlerDifferential_map_comp_mapBaseChange_stalk_pullback.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.StalkDifferentialBaseChange

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

theorem _root_.AlgebraicGeometry.bijective_kaehlerDifferential_map_comp_mapBaseChange_stalk_pullback
    {R : Type u} [CommRing R] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (z : Z ⟶ Spec (CommRingCat.of R))
    (p : ↥(pullback z f))
    [Algebra R (Z.presheaf.stalk ((pullback.fst z f).base p))]
    (halgZ : Z.fromSpecStalk ((pullback.fst z f).base p) ≫ z =
      Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ((pullback.fst z f).base p)))))
    [Algebra R (X.presheaf.stalk ((pullback.snd z f).base p))]
    (halgX : X.fromSpecStalk ((pullback.snd z f).base p) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ((pullback.snd z f).base p)))))
    [Algebra R ((pullback z f).presheaf.stalk p)] :
    let : Algebra (Z.presheaf.stalk ((pullback.fst z f).base p)) ((pullback z f).presheaf.stalk
        p) :=
      ((pullback.fst z f).stalkMap p).hom.toAlgebra
    let : Algebra (X.presheaf.stalk ((pullback.snd z f).base p)) ((pullback z f).presheaf.stalk
        p) :=
      ((pullback.snd z f).stalkMap p).hom.toAlgebra
    ∀ [IsScalarTower R (Z.presheaf.stalk ((pullback.fst z f).base p)) ((pullback z
        f).presheaf.stalk p)]
      [IsScalarTower R (X.presheaf.stalk ((pullback.snd z f).base p)) ((pullback z
          f).presheaf.stalk p)],
      Function.Bijective
        ((KaehlerDifferential.map R (Z.presheaf.stalk ((pullback.fst z f).base p))
              ((pullback z f).presheaf.stalk p) ((pullback z f).presheaf.stalk p)).restrictScalars
            ((pullback z f).presheaf.stalk p) ∘ₗ
          KaehlerDifferential.mapBaseChange R (X.presheaf.stalk ((pullback.snd z f).base p))
            ((pullback z f).presheaf.stalk p)) := by
  intro algA algB hTA hTB
  obtain ⟨𝔔, h𝔔, e, he₁, he₂⟩ :=
      AlgebraicGeometry.exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_stalk f z
      p halgZ halgX
  have : 𝔔.IsPrime := h𝔔
  let algT : Algebra ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk
      ((pullback.snd z f).base p))) ((pullback z f).presheaf.stalk p) :=
    (e.symm.toRingHom.comp (algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R]
        (X.presheaf.stalk ((pullback.snd z f).base p))) (Localization.AtPrime 𝔔))).toAlgebra
  let eT : Localization.AtPrime 𝔔 ≃ₐ[((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R]
      (X.presheaf.stalk ((pullback.snd z f).base p)))] ((pullback z f).presheaf.stalk p) :=
    AlgEquiv.ofRingEquiv (f := e.symm) (fun _ => rfl)
  have : IsLocalization 𝔔.primeCompl ((pullback z f).presheaf.stalk p) :=
    IsLocalization.isLocalization_of_algEquiv 𝔔.primeCompl eT
  have : IsScalarTower (Z.presheaf.stalk ((pullback.fst z f).base p)) ((Z.presheaf.stalk
      ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base p))) ((pullback
      z f).presheaf.stalk p) :=
    IsScalarTower.of_algebraMap_eq (R := (Z.presheaf.stalk ((pullback.fst z f).base p))) (S :=
        ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk ((pullback.snd z
        f).base p)))) (A := ((pullback z f).presheaf.stalk p)) fun s => by
    change ((pullback.fst z f).stalkMap p).hom s =
      e.symm (algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk
          ((pullback.snd z f).base p))) (Localization.AtPrime 𝔔) (algebraMap (Z.presheaf.stalk
          ((pullback.fst z f).base p)) ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R]
          (X.presheaf.stalk ((pullback.snd z f).base p))) s))
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, ← he₁,
      RingEquiv.symm_apply_apply]
  have hB : (algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk
      ((pullback.snd z f).base p))) ((pullback z f).presheaf.stalk p)).comp
      (Algebra.TensorProduct.includeRight (R := R) (A := (Z.presheaf.stalk ((pullback.fst z
          f).base p))) (B := (X.presheaf.stalk ((pullback.snd z f).base p)))).toRingHom =
      algebraMap (X.presheaf.stalk ((pullback.snd z f).base p)) ((pullback z f).presheaf.stalk p)
          := by
    refine RingHom.ext fun t => ?_
    change e.symm (algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R]
        (X.presheaf.stalk ((pullback.snd z f).base p))) (Localization.AtPrime 𝔔)
        (Algebra.TensorProduct.includeRight t)) =
      ((pullback.snd z f).stalkMap p).hom t
    rw [Algebra.TensorProduct.includeRight_apply, ← he₂, RingEquiv.symm_apply_apply]
  have : IsLocalization (⊥ : Submonoid (Z.presheaf.stalk ((pullback.fst z f).base p)))
      (Z.presheaf.stalk ((pullback.fst z f).base p)) := IsLocalization.self bot_le
  exact KaehlerDifferential.bijective_map_comp_mapBaseChange_of_isLocalization_tensorProduct R
      (Z.presheaf.stalk ((pullback.fst z f).base p)) (Z.presheaf.stalk ((pullback.fst z f).base
      p)) (X.presheaf.stalk ((pullback.snd z f).base p)) ((pullback z f).presheaf.stalk p)
    (⊥ : Submonoid (Z.presheaf.stalk ((pullback.fst z f).base p))) hB 𝔔.primeCompl

end AbelianVarieties.NOSProofs.StalkDifferentialBaseChange

end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_maximalIdeal_stalk_pullback_le_of_sections.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

theorem _root_.AlgebraicGeometry.maximalIdeal_stalk_pullback_le_of_sections
    {k : Type u} [Field k] {Y Z : Scheme.{u}} (pY : Y ⟶ Spec (.of k)) (pZ : Z ⟶ Spec (.of k))
    (y : Spec (.of k) ⟶ Y) (hy : y ≫ pY = 𝟙 _) (z : Spec (.of k) ⟶ Z) (hz : z ≫ pZ = 𝟙 _)
    (w : ↑(pullback pY pZ)) (hw : w = (pullback.lift y z (hy.trans hz.symm)) (closedPoint k)) :
    maximalIdeal ((pullback pY pZ).presheaf.stalk w) ≤
      (maximalIdeal _).map ((pullback.fst pY pZ).stalkMap w).hom ⊔
        (maximalIdeal _).map ((pullback.snd pY pZ).stalkMap w).hom := by
  subst hw
  exact (maximalIdeal_stalk_pullback_eq_map_stalkMap_fst_sup_map_stalkMap_snd_of_section
    pY pZ y hy z hz).le

end
