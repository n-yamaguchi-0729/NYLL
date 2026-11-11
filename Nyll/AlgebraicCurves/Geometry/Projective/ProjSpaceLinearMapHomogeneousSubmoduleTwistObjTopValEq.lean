/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Geometry.Projective.HomogeneousChartSections
public import Mathlib.Tactic.Ring
public import Nyll.SchemeTheory.ProjectiveSpace.Basic
public import Nyll.AlgebraicCurves.Geometry.Projective.ProjTwistDatum

/-!
# Proj Space exists linear Map homogeneous Submodule twist Obj top val eq
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Geometry.Projective.Proofs
namespace ProjSpace_exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

open HomogeneousLocalization

namespace P2mWs6E1Aux

theorem map_appTop_π_eq_awayToSection_algebraMap (k : Type u) [CommRing k] (n : ℕ) (i : Fin (n +
  1)) (r : k) :
    (Proj (homogeneousSubmodule (Fin (n + 1)) k)).presheaf.map
        (homOfLE (le_top : Proj.basicOpen (homogeneousSubmodule (Fin (n + 1)) k) (X i) ≤ ⊤)).op
        ((ProjSpace.π k n).appTop ((Scheme.ΓSpecIso (.of k)).inv r))
      = Proj.awayToSection (homogeneousSubmodule (Fin (n + 1)) k) (X i)
          (algebraMap k (Away (homogeneousSubmodule (Fin (n + 1)) k) (X i)) r) :=
  ProjSpace.HomogeneousChartSections.map_appTop_π_eq_awayToSection_algebraMap k n i r

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

theorem pullAway_algebraMap (i : Fin (n + 1)) (c : k) {W : Z.Opens} (hW : W ≤
  ProjSpace.pullbackChart φ i) :
    ProjSpace.restrictFun hW (pullAway φ i (algebraMap k (Away 𝒜 (X i)) c))
      = (Scheme.TwoAffineOpenCover.algebraOfHom (φ ≫ ProjSpace.π k n) W).algebraMap c :=
  ProjSpace.HomogeneousChartSections.pullAway_algebraMap φ i c hW

end Comp

end P2mWs6E1Aux

open P2mWs6E1Aux in
theorem _root_.AlgebraicGeometry.ProjSpace.exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq
    {k : Type u} [CommRing k] {n : ℕ} {Z : Scheme.{u}}
    (φ : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) (d : ℕ) :
    ∃ θ : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d) →ₗ[k]
        ProjSpace.twistObj (φ ≫ ProjSpace.π k n) φ d ⊤,
      (∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d) (i : Fin (n + 1)),
        (θ ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩).val i =
          ProjSpace.restrictFun (inf_le_right : ⊤ ⊓ ProjSpace.pullbackChart φ i ≤
            ProjSpace.pullbackChart φ i)
            ((φ.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
              (MvPolynomial.X i)))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
                (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ })))) ∧
      (∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
        θ ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩ = 0 ↔
          ∀ i : Fin (n + 1),
            (φ.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
              (MvPolynomial.X i)))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
                (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ })) = 0) := by
  classical
  let comp : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d) → ∀ i : Fin (n + 1),
      Γ(Z, (⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart φ i) :=
    fun p i => ProjSpace.restrictFun inf_le_right (pullAway φ i (frac d p i))
  have hcompat : ∀ p, ProjSpace.TwistCompat φ d ⊤ (comp p) := by
    intro p i j
    have hV : ((⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart φ i) ⊓ ProjSpace.pullbackChart φ j ≤
      ProjSpace.pullbackOverlap φ i j := by
      rw [ProjSpace.pullbackOverlap_eq_inf]; exact le_inf (inf_le_left.trans inf_le_right)
        inf_le_right
    change ProjSpace.restrictFun _ (ProjSpace.restrictFun _ (pullAway φ i (frac d p i)))
      = ProjSpace.restrictFun _ (ProjSpace.frameUnit φ i j) ^ d *
          ProjSpace.restrictFun _ (ProjSpace.restrictFun _ (pullAway φ j (frac d p j)))
    rw [ProjSpace.restrictFun_restrictFun, ProjSpace.restrictFun_restrictFun]
    have e1 : ProjSpace.restrictFun (inf_le_left.trans inf_le_right :
          ((⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart φ i) ⊓ ProjSpace.pullbackChart φ j ≤
            ProjSpace.pullbackChart φ i)
          (pullAway φ i (frac d p i))
        = ProjSpace.restrictFun hV (ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_left φ i j)
          (pullAway φ i (frac d p i))) := by
      rw [ProjSpace.restrictFun_restrictFun]
    have e2 : ProjSpace.restrictFun (inf_le_right :
          ((⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart φ i) ⊓ ProjSpace.pullbackChart φ j ≤
            ProjSpace.pullbackChart φ j)
          (pullAway φ j (frac d p j))
        = ProjSpace.restrictFun hV (ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_right φ i
          j) (pullAway φ j (frac d p j))) := by
      rw [ProjSpace.restrictFun_restrictFun]
    have e3 : ProjSpace.restrictFun (inf_le_left.trans inf_le_right :
          ((⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart φ i) ⊓ ProjSpace.pullbackChart φ j ≤
            ProjSpace.pullbackChart φ i)
          (ProjSpace.frameUnit φ i j)
        = ProjSpace.restrictFun hV (ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_left φ i j)
          (ProjSpace.frameUnit φ i j)) := by
      rw [ProjSpace.restrictFun_restrictFun]
    rw [e1, e2, e3, restrictFun_pullAway_frac, map_mul, map_pow]
  let θfun : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d) → ProjSpace.twistObj (φ ≫
    ProjSpace.π k n) φ d ⊤ :=
    fun p => ⟨comp p, hcompat p⟩
  have hval : ∀ p i, (θfun p).val i = ProjSpace.restrictFun inf_le_right (pullAway φ i (frac d p
    i)) := fun _ _ => rfl
  refine ⟨{ toFun := θfun, map_add' := ?_, map_smul' := ?_ }, ?_, ?_⟩
  · intro p q
    refine ProjSpace.twistObj.ext (funext fun i => ?_)
    rw [ProjSpace.twistObj.add_val, Pi.add_apply, hval, hval, hval, frac_add, pullAway_add, map_add]
  · intro c p
    refine ProjSpace.twistObj.ext (funext fun i => ?_)
    rw [hval, RingHom.id_apply, ProjSpace.twistObj.algebraMap_smul, ProjSpace.twistObj.smul_val,
      hval, frac_smul,
      pullAway_mul, map_mul]
    congr 1
    rw [pullAway_algebraMap φ i c, ProjSpace.restrictFun_algebraMap']
  · intro F hF i
    rfl
  · intro F hF
    constructor
    · intro h i
      have hi := congrArg (fun g => g.val i) h
      simp only [ProjSpace.twistObj.zero_val, Pi.zero_apply] at hi
      change ProjSpace.restrictFun inf_le_right (pullAway φ i (frac d ⟨F, _⟩ i)) = 0 at hi
      have hback : ∀ x : Γ(Z, ProjSpace.pullbackChart φ i),
          ProjSpace.restrictFun (le_inf le_top le_rfl : ProjSpace.pullbackChart φ i ≤ (⊤ : Z.Opens)
            ⊓ ProjSpace.pullbackChart φ i)
            (ProjSpace.restrictFun inf_le_right x) = x := fun x => by
        rw [ProjSpace.restrictFun_restrictFun, ProjSpace.restrictFun_refl]
      have := hback (pullAway φ i (frac d ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
        i))
      rw [hi, map_zero] at this
      exact this.symm
    · intro h
      refine ProjSpace.twistObj.ext (funext fun i => ?_)
      rw [ProjSpace.twistObj.zero_val, Pi.zero_apply]
      change ProjSpace.restrictFun inf_le_right (pullAway φ i (frac d ⟨F, _⟩ i)) = 0
      rw [pullAway_eq]
      exact (congrArg _ (h i)).trans (map_zero _)
end ProjSpace_exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq
end AlgebraicCurves.Geometry.Projective.Proofs
end ProofImplementation
