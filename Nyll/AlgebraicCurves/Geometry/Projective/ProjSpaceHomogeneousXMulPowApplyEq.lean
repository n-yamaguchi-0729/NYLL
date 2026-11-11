/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Geometry.Projective.HomogeneousChartSections
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.NormCast
public import Nyll.SchemeTheory.ProjectiveSpace.Basic
public import Nyll.SchemeTheory.ProjectiveSpace.Cover
public import Nyll.AlgebraicCurves.Geometry.Projective.ProjTwistDatum

/-!
# Proj Space exists is Homogeneous forall x Mul pow apply eq of is Closed Immersion
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Geometry.Projective.Proofs
namespace ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

open HomogeneousLocalization

namespace SatUnitBody

section Frac

variable {k : Type u} [CommRing k] {n : ℕ}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k

/-- The homogeneous fraction with the given numerator and a matching power of the chosen
coordinate. -/
noncomputable def frac (d : ℕ) (p : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) (i :
  Fin (n + 1)) : Away 𝒜 (X i) :=
  ProjSpace.HomogeneousChartSections.frac d p i

theorem val_frac (d : ℕ) (p : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) (i : Fin (n +
  1)) :
    (frac d p i).val = Localization.mk p.1 (⟨MvPolynomial.X i ^ d, ⟨d, rfl⟩⟩ : Submonoid.powers
      (MvPolynomial.X i)) :=
  ProjSpace.HomogeneousChartSections.val_frac d p i

theorem frac_add (d : ℕ) (p q : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) (i : Fin (n
  + 1)) :
    frac d (p + q) i = frac d p i + frac d q i :=
  ProjSpace.HomogeneousChartSections.frac_add d p q i

theorem frac_smul (d : ℕ) (c : k) (p : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) (i :
  Fin (n + 1)) :
    frac d (c • p) i = algebraMap k (Away 𝒜 (X i)) c * frac d p i :=
  ProjSpace.HomogeneousChartSections.frac_smul d c p i

theorem awayMap_frac_eq (d : ℕ) (p : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) (i j :
  Fin (n + 1)) :
    awayMap 𝒜 (ProjSpace.X_mem_one k n j) rfl (frac d p i)
      = awayMap 𝒜 (ProjSpace.X_mem_one k n j) rfl (ProjSpace.ratio k n i j) ^ d
          * awayMap 𝒜 (ProjSpace.X_mem_one k n i)
              (mul_comm (X i) (X j) : (X i * X j : MvPolynomial (Fin (n + 1)) k) = X j * X i) (frac
                d p j) :=
  ProjSpace.HomogeneousChartSections.awayMap_frac_eq d p i j

end Frac

section Comp

variable {k : Type u} [CommRing k] {n : ℕ} {Z : Scheme.{u}}
  (φ : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k

/-- The section on a pulled-back projective chart induced by a homogeneous localization element. -/
noncomputable def pullAway (i : Fin (n + 1)) (a : Away 𝒜 (X i)) : Γ(Z, ProjSpace.pullbackChart φ i)
  :=
  ProjSpace.HomogeneousChartSections.pullAway φ i a

theorem pullAway_eq (i : Fin (n + 1)) (a : Away 𝒜 (X i)) :
    pullAway φ i a = (φ.app (Proj.basicOpen 𝒜 (X i))) (Proj.awayToSection 𝒜 (X i) a) :=
  ProjSpace.HomogeneousChartSections.pullAway_eq φ i a

theorem pullAway_add (i : Fin (n + 1)) (a b : Away 𝒜 (X i)) :
    pullAway φ i (a + b) = pullAway φ i a + pullAway φ i b :=
  ProjSpace.HomogeneousChartSections.pullAway_add φ i a b

theorem pullAway_mul (i : Fin (n + 1)) (a b : Away 𝒜 (X i)) :
    pullAway φ i (a * b) = pullAway φ i a * pullAway φ i b :=
  ProjSpace.HomogeneousChartSections.pullAway_mul φ i a b

theorem pullAway_zero (i : Fin (n + 1)) : pullAway φ i 0 = 0 :=
  ProjSpace.HomogeneousChartSections.pullAway_zero φ i

theorem restrictFun_pullAway_left (i j : Fin (n + 1)) (a : Away 𝒜 (X i)) :
    ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_left φ i j) (pullAway φ i a)
      = (φ.app (Proj.basicOpen 𝒜 (X i * X j))).hom
          ((Proj.awayToSection 𝒜 (X i * X j)).hom (awayMap 𝒜 (ProjSpace.X_mem_one k n j) rfl a)) :=
  ProjSpace.HomogeneousChartSections.restrictFun_pullAway_left φ i j a

theorem restrictFun_pullAway_right (i j : Fin (n + 1)) (a : Away 𝒜 (X j)) :
    ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_right φ i j) (pullAway φ j a)
      = (φ.app (Proj.basicOpen 𝒜 (X i * X j))).hom
          ((Proj.awayToSection 𝒜 (X i * X j)).hom (awayMap 𝒜 (ProjSpace.X_mem_one k n i)
            (mul_comm (X i) (X j) : (X i * X j : MvPolynomial (Fin (n + 1)) k) = X j * X i) a)) :=
  ProjSpace.HomogeneousChartSections.restrictFun_pullAway_right φ i j a

theorem restrictFun_pullAway_frac (d : ℕ) (p : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k
  d)) (i j : Fin (n + 1)) :
    ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_left φ i j) (pullAway φ i (frac d p i))
      = ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_left φ i j) (ProjSpace.frameUnit φ i j)
        ^ d
          * ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_right φ i j) (pullAway φ j (frac d
            p j)) :=
  ProjSpace.HomogeneousChartSections.restrictFun_pullAway_frac φ d p i j

end Comp

section Main

variable {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
  (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A))

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A

theorem frameUnit_eq_pullAway (i j : Fin (n + 1)) :
    ProjSpace.frameUnit ι i j = pullAway ι i (ProjSpace.ratio A n i j) :=
  ProjSpace.HomogeneousChartSections.frameUnit_eq_pullAway ι i j

theorem xMul_pow_apply (j : Fin (n + 1)) (k : ℕ) (f : ProjSpace.twistFam (ι ≫ ProjSpace.π A n) ι)
  (d : ℤ) (i : Fin (n + 1)) :
    (((ProjSpace.twistGradedModule ι (ι ≫ ProjSpace.π A n)).xMul j ^ k) f) d i =
      ProjSpace.restrictFun (inf_le_right : (⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart ι i ≤
        ProjSpace.pullbackChart ι i)
        (ProjSpace.frameUnit ι i j) ^ k * f (d - k) i :=
  ProjSpace.HomogeneousChartSections.xMul_pow_apply ι j k f d i

theorem exists_eq_pullAway_mk [IsClosedImmersion ι] (j : Fin (n + 1)) (z : Γ(Z,
  ProjSpace.pullbackChart ι j)) :
    ∃ (a : ℕ) (G : MvPolynomial (Fin (n + 1)) A) (hG : G ∈ 𝒜 a),
      z = pullAway ι j (Away.mk 𝒜 (ProjSpace.X_mem_one A n j) a G (by simpa using hG)) :=
  ProjSpace.HomogeneousChartSections.exists_eq_pullAway_mk ι j z

theorem basicOpen_frameUnit_le (i j : Fin (n + 1)) :
    Z.basicOpen (ProjSpace.frameUnit ι i j) ≤ ProjSpace.pullbackChart ι j :=
  ProjSpace.HomogeneousChartSections.basicOpen_frameUnit_le ι i j

theorem exists_pow_mul_eq_zero [IsClosedImmersion ι] (i j : Fin (n + 1)) (δ : Γ(Z,
  ProjSpace.pullbackChart ι i))
    (hδ : ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_left ι i j) δ = 0) :
    ∃ N : ℕ, ProjSpace.frameUnit ι i j ^ N * δ = 0 :=
  ProjSpace.HomogeneousChartSections.exists_pow_mul_eq_zero ι i j δ hδ

theorem pullAway_pow (i : Fin (n + 1)) (a : Away 𝒜 (X i)) (N : ℕ) :
    pullAway ι i (a ^ N) = pullAway ι i a ^ N :=
  ProjSpace.HomogeneousChartSections.pullAway_pow ι i a N

theorem frac_congr {d₁ d₂ : ℕ} (h : d₁ = d₂) (p : ↥(𝒜 d₁)) (i : Fin (n + 1)) :
    frac d₁ p i = frac d₂ ⟨p.1, h ▸ p.2⟩ i :=
  ProjSpace.HomogeneousChartSections.frac_congr h p i

theorem frameUnit_pow_mul_pullAway_frac (i j : Fin (n + 1)) (N d : ℕ) (p : ↥(𝒜 d)) :
    ProjSpace.frameUnit ι i j ^ N * pullAway ι i (frac d p i) =
      pullAway ι i (frac (d + N) ⟨X j ^ N * p.1, by
        have h := SetLike.mul_mem_graded (SetLike.pow_mem_graded N (ProjSpace.X_mem_one A n j)) p.2
        rwa [smul_eq_mul, mul_one, Nat.add_comm N d] at h⟩ i) :=
  ProjSpace.HomogeneousChartSections.frameUnit_pow_mul_pullAway_frac ι i j N d p

end Main

end SatUnitBody

end ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion
end AlgebraicCurves.Geometry.Projective.Proofs

namespace AlgebraicGeometry

universe u

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.MvPolynomial _root_.TensorProduct _root_.HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra

open _root_.AlgebraicCurves.Geometry.Projective.Proofs in
open ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion in
open SatUnitBody in
theorem ProjSpace.exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion
    {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsClosedImmersion ι]
    (e : ℕ) (m : ProjSpace.twistFam (ι ≫ ProjSpace.π A n) ι)
    (hm : m ∈ (ProjSpace.twistGradedModule ι (ι ≫ ProjSpace.π A n)).grade (e : ℤ)) (j : Fin (n +
      1)) :
    ∃ (k : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous (e + k)),
      ∀ i : Fin (n + 1),
        (((ProjSpace.twistGradedModule ι (ι ≫ ProjSpace.π A n)).xMul j ^ k) m) ((e + k : ℕ) : ℤ) i =
          ProjSpace.restrictFun
            (inf_le_right : (⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart ι i ≤ ProjSpace.pullbackChart ι
              i)
            ((ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
              (MvPolynomial.X i)))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
                (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := e + k
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule (e + k) F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ (e + k), (MvPolynomial.mem_homogeneousSubmodule (e +
                      k) _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i (e + k))⟩
                    den_mem := ⟨e + k, rfl⟩ }))) := by
  classical
  have hXi : ∀ i : Fin (n + 1), (X i : MvPolynomial (Fin (n + 1)) A) ∈
    MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A 1 :=
    fun i => ProjSpace.X_mem_one A n i
  have hWU : ∀ i : Fin (n + 1), ((⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart ι i) ≤
    ProjSpace.pullbackChart ι i :=
    fun i => inf_le_right
  have hUW : ∀ i : Fin (n + 1), ProjSpace.pullbackChart ι i ≤ (⊤ : Z.Opens) ⊓
    ProjSpace.pullbackChart ι i :=
    fun i => le_inf le_top le_rfl
  have hVW : ∀ i : Fin (n + 1), ProjSpace.pullbackOverlap ι i j ≤ (⊤ : Z.Opens) ⊓
    ProjSpace.pullbackChart ι i :=
    fun i => (ProjSpace.pullbackOverlap_le_left ι i j).trans (hUW i)
  have hVWj : ∀ i : Fin (n + 1), ProjSpace.pullbackOverlap ι i j ≤ (⊤ : Z.Opens) ⊓
    ProjSpace.pullbackChart ι j :=
    fun i => (ProjSpace.pullbackOverlap_le_right ι i j).trans (hUW j)
  have rt : ∀ (i : Fin (n + 1)) (x : Γ(Z, (⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart ι i)),
      ProjSpace.restrictFun (hWU i) (ProjSpace.restrictFun (hUW i) x) = x := fun i x => by
    rw [ProjSpace.restrictFun_restrictFun]; exact ProjSpace.restrictFun_refl x
  have rt' : ∀ (i : Fin (n + 1)) (y : Γ(Z, ProjSpace.pullbackChart ι i)),
      ProjSpace.restrictFun (hUW i) (ProjSpace.restrictFun (hWU i) y) = y := fun i y => by
    rw [ProjSpace.restrictFun_restrictFun]; exact ProjSpace.restrictFun_refl y
  have hcomp : ProjSpace.TwistCompat ι e ⊤ (m (e : ℤ)) := by
    have h := hm.2.2 (by exact_mod_cast Nat.zero_le e)
    simpa only [Int.toNat_natCast] using h
  obtain ⟨a, G, hG, hmj⟩ := exists_eq_pullAway_mk ι j (ProjSpace.restrictFun (hUW j) (m (e : ℤ) j))
  have hGa : G ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A (a • 1) := by simpa using hG
  let p₀ : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A (e + a)) := ⟨X j ^ e * G, by
    have h := SetLike.mul_mem_graded (SetLike.pow_mem_graded e (hXi j)) hG
    rwa [smul_eq_mul, mul_one] at h⟩
  let f : ∀ i : Fin (n + 1), Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i * X j)
    →+*
      Γ(Z, ProjSpace.pullbackOverlap ι i j) := fun i =>
    (ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i * X
      j))).hom.comp
      (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i * X j)).hom
  have hf : ∀ (i : Fin (n + 1)) x, f i x =
      (ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i * X j))).hom
        ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i * X j)).hom
          x) := fun _ _ => rfl
  have claim2 : ∀ i : Fin (n + 1),
      ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_left ι i j)
        (ProjSpace.frameUnit ι i j ^ a * ProjSpace.restrictFun (hUW i) (m (e : ℤ) i)) =
      ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_left ι i j) (pullAway ι i (frac (e + a)
        p₀ i)) := by
    intro i
    have hc := congrArg (ProjSpace.restrictFun (le_inf (hVW i) (ProjSpace.pullbackOverlap_le_right
      ι i j) :
      ProjSpace.pullbackOverlap ι i j ≤ ((⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart ι i) ⊓
        ProjSpace.pullbackChart ι j))
      (hcomp i j)
    simp only [map_mul, map_pow, ProjSpace.restrictFun_restrictFun] at hc
    have hmjV : ProjSpace.restrictFun (hVWj i) (m (e : ℤ) j) =
        ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_right ι i j)
          (pullAway ι j (Away.mk _ (hXi j) a G hGa)) := by
      rw [← hmj, ProjSpace.restrictFun_restrictFun]
    rw [map_mul, map_pow, ProjSpace.restrictFun_restrictFun,
      ProjSpace.restrictFun_irrel ((ProjSpace.pullbackOverlap_le_left ι i j).trans (hUW i)) (hVW i),
      ProjSpace.restrictFun_irrel _ (hVW i) (m (e : ℤ) i)] at *
    rw [hc, ProjSpace.restrictFun_irrel _ (hVWj i) (m (e : ℤ) j), hmjV, restrictFun_pullAway_right,
      ProjSpace.restrictFun_frameUnit_left, restrictFun_pullAway_left, ← hf, ← hf, ← hf, ← map_pow
        (f i), ← map_pow (f i),
      ← map_mul (f i), ← map_mul (f i)]
    congr 1
    apply HomogeneousLocalization.val_injective
    rw [val_mul, val_mul, val_pow, val_pow, frac, ProjSpace.HomogeneousChartSections.frac,
      val_awayMap_mk, HomogeneousLocalization.Away.mk,
      val_awayMap_mk,
      ProjSpace.val_awayMap_ratio A n i j j (hXi j) rfl _ (X j)
        (by rw [ProjSpace.ratio, HomogeneousLocalization.Away.val_mk]),
      Localization.mk_pow, Localization.mk_pow, Localization.mk_mul, Localization.mk_mul,
        Localization.mk_eq_mk_iff,
      Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, SubmonoidClass.coe_pow]
    ring
  have hkill : ∀ i : Fin (n + 1), ∃ N : ℕ, ProjSpace.frameUnit ι i j ^ N *
      (ProjSpace.frameUnit ι i j ^ a * ProjSpace.restrictFun (hUW i) (m (e : ℤ) i) - pullAway ι i
        (frac (e + a) p₀ i)) = 0 := by
    intro i
    apply exists_pow_mul_eq_zero ι i j
    rw [map_sub, claim2 i, sub_self]
  choose Nf hNf using hkill
  let N : ℕ := ∑ i, Nf i
  have hNle : ∀ i, Nf i ≤ N := fun i => Finset.single_le_sum (fun i _ => Nat.zero_le (Nf i))
    (Finset.mem_univ i)
  have hFhom : (X j ^ N * (X j ^ e * G) : MvPolynomial (Fin (n + 1)) A).IsHomogeneous (e + (a + N))
    := by
    have h := (MvPolynomial.isHomogeneous_X_pow j N).mul ((MvPolynomial.isHomogeneous_X_pow j e).mul
      ((MvPolynomial.mem_homogeneousSubmodule a G).mp hG))
    convert h using 1; omega
  refine ⟨a + N, X j ^ N * (X j ^ e * G), hFhom, fun i => ?_⟩
  have hinj : Function.Injective (ProjSpace.restrictFun (hUW i)) := fun x y hxy => by
    rw [← rt i x, ← rt i y, hxy]
  apply hinj
  erw [xMul_pow_apply, map_mul, map_pow, rt', rt']
  have hidx : ((e + (a + N) : ℕ) : ℤ) - ((a + N : ℕ) : ℤ) = (e : ℤ) := by push_cast; ring
  rw [hidx]
  change ProjSpace.frameUnit ι i j ^ (a + N) * ProjSpace.restrictFun (hUW i) (m (e : ℤ) i) =
    pullAway ι i (frac (e + (a + N)) ⟨X j ^ N * (X j ^ e * G),
      (MvPolynomial.mem_homogeneousSubmodule (e + (a + N)) _).mpr hFhom⟩ i)
  have hsplit : ProjSpace.frameUnit ι i j ^ (a + N) * ProjSpace.restrictFun (hUW i) (m (e : ℤ) i) =
      ProjSpace.frameUnit ι i j ^ N * pullAway ι i (frac (e + a) p₀ i) +
      ProjSpace.frameUnit ι i j ^ (N - Nf i) * (ProjSpace.frameUnit ι i j ^ Nf i *
        (ProjSpace.frameUnit ι i j ^ a * ProjSpace.restrictFun (hUW i) (m (e : ℤ) i) - pullAway ι i
          (frac (e + a) p₀ i))) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (hNle i)]
    ring
  rw [hsplit, hNf i, mul_zero, add_zero, frameUnit_pow_mul_pullAway_frac,
    frac_congr (show e + a + N = e + (a + N) by omega)]
end AlgebraicGeometry
end ProofImplementation
