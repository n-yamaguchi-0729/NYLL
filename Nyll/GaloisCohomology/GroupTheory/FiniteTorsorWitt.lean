/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.GroupTheory.FiniteTorsorInvariants
public import Nyll.GaloisCohomology.ArtinSchreier.WittCharacterSurjectivity
public import Nyll.GaloisCohomology.ArtinSchreier.WittCharacters

/-!
# Prime-power characters of an actual affine torsor

Faithfully flat torsor trace one lifts to Witt trace one over the original
coordinate ring. Finite additive Hilbert 90 and coefficientwise faithfully
flat descent then realize every cyclic prime-power character by an actual
Artin–Schreier–Witt equation over the original base ring.
-/

@[expose] public section

noncomputable section

namespace GaloisCohomology.FiniteTorsor

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  {G : Type*} [Group G] [Fintype G] (ρ : G →* (S ≃ₐ[R] S))
  (p : ℕ) [Fact p.Prime] [CharP S p]

/-- A trace-one section lifts to an actual Witt trace-one section over an
arbitrary commutative ring of characteristic `p`. -/
theorem exists_witt_sum_eq_one (t : S) (ht : ∑ g, ρ g t = 1) :
    ∃ w : WittVector p S, ∑ g, WittVector.map (ρ g).toRingHom w = 1 := by
  classical
  let s : WittVector p S :=
    ∑ g : G, WittVector.map (ρ g).toRingHom (WittVector.teichmuller p t)
  have hs0 : s.coeff 0 = 1 := by
    change WittVector.constantCoeff s = 1
    rw [map_sum]
    change (∑ g : G, ρ g t) = 1
    exact ht
  have hsfix (g : G) : WittVector.map (ρ g).toRingHom s = s := by
    rw [map_sum]
    have hcomp (h : G) :
        WittVector.map (ρ g).toRingHom
            (WittVector.map (ρ h).toRingHom (WittVector.teichmuller p t)) =
          WittVector.map (ρ (g * h)).toRingHom (WittVector.teichmuller p t) := by
      apply WittVector.ext
      intro i
      change ρ g (ρ h ((WittVector.teichmuller p t).coeff i)) =
        ρ (g * h) ((WittVector.teichmuller p t).coeff i)
      rw [map_mul]
      rfl
    simp only [hcomp]
    exact Fintype.sum_bijective (fun h : G => g * h)
      (Group.mulLeft_bijective g) _ _ (fun _ => rfl)
  let u : (WittVector p S)ˣ := WittVector.mkUnit (a := (1 : Sˣ)) hs0
  have hu : (u : WittVector p S) = s := rfl
  let v : WittVector p S := ↑u⁻¹
  have hsv : s * v = 1 := u.mul_inv_of_eq hu
  have hvs : v * s = 1 := u.inv_mul_of_eq hu
  have hvfix (g : G) : WittVector.map (ρ g).toRingHom v = v := by
    have hg := congrArg (WittVector.map (ρ g).toRingHom) hsv
    rw [map_mul, hsfix, map_one] at hg
    calc
      WittVector.map (ρ g).toRingHom v = (v * s) * WittVector.map (ρ g).toRingHom v := by
        rw [hvs, one_mul]
      _ = v * (s * WittVector.map (ρ g).toRingHom v) := mul_assoc _ _ _
      _ = v := by rw [hg, mul_one]
  refine ⟨WittVector.teichmuller p t * v, ?_⟩
  calc
    (∑ g : G, WittVector.map (ρ g).toRingHom (WittVector.teichmuller p t * v)) =
        ∑ g : G, WittVector.map (ρ g).toRingHom (WittVector.teichmuller p t) * v := by
      apply Finset.sum_congr rfl
      intro g _
      rw [map_mul, hvfix]
    _ = s * v := (Finset.sum_mul _ _ _).symm
    _ = 1 := hsv

/-- Trace-one averaging kills every cocycle in a finite Witt ring. -/
theorem wittAdditiveHilbert90_of_trace_one (m : ℕ) (t : S) (ht : ∑ g, ρ g t = 1)
    (c : G → TruncatedWittVector p m S)
    (hc : ∀ g h : G, c (g * h) = TruncatedWittVector.map (ρ g).toRingHom (c h) + c g) :
    ∃ β : TruncatedWittVector p m S, ∀ g : G,
      TruncatedWittVector.map (ρ g).toRingHom β - β = c g := by
  classical
  obtain ⟨w, hw⟩ := exists_witt_sum_eq_one R S ρ p t ht
  let a : TruncatedWittVector p m S := WittVector.truncate m w
  have ha : (∑ h : G, TruncatedWittVector.map (ρ h).toRingHom a) = 1 := by
    have h := congrArg (WittVector.truncate m) hw
    rw [map_sum, map_one] at h
    simpa only [a, TruncatedWittVector.map_wittVector_truncate] using h
  let B : TruncatedWittVector p m S :=
    ∑ h : G, c h * TruncatedWittVector.map (ρ h).toRingHom a
  have hB (g : G) : TruncatedWittVector.map (ρ g).toRingHom B = B - c g := by
    have hperm : (∑ h : G, c (g * h) * TruncatedWittVector.map (ρ (g * h)).toRingHom a) = B :=
      Fintype.sum_bijective (fun h : G => g * h) (Group.mulLeft_bijective g)
        _ _ (fun _ => rfl)
    have hpermTrace : (∑ h : G, TruncatedWittVector.map (ρ (g * h)).toRingHom a) = 1 := by
      rw [Fintype.sum_bijective (fun h : G => g * h) (Group.mulLeft_bijective g)
        _ (fun h => TruncatedWittVector.map (ρ h).toRingHom a) (fun _ => rfl)]
      exact ha
    have hcomp (h : G) :
        TruncatedWittVector.map (ρ g).toRingHom (TruncatedWittVector.map (ρ h).toRingHom a) =
          TruncatedWittVector.map (ρ (g * h)).toRingHom a := by
      apply TruncatedWittVector.ext
      intro i
      simp only [TruncatedWittVector.map_coeff]
      change ρ g (ρ h (a.coeff i)) = ρ (g * h) (a.coeff i)
      rw [map_mul]
      rfl
    calc
      TruncatedWittVector.map (ρ g).toRingHom B =
          ∑ h : G, (c (g * h) - c g) * TruncatedWittVector.map (ρ (g * h)).toRingHom a := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro h _
        rw [map_mul, hc, add_sub_cancel_right, hcomp]
      _ = (∑ h : G, c (g * h) * TruncatedWittVector.map (ρ (g * h)).toRingHom a) -
          c g * (∑ h : G, TruncatedWittVector.map (ρ (g * h)).toRingHom a) := by
        simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
      _ = B - c g := by rw [hperm, hpermTrace, mul_one]
  refine ⟨-B, ?_⟩
  intro g
  rw [map_neg, hB]
  ring

variable [Module.FaithfullyFlat R S]

omit [CharP S p] [Fintype G] in
/-- Fixed Witt vectors descend through the original affine torsor. -/
theorem exists_witt_base_of_fixed (m : ℕ) (hinj : Function.Injective (tensorMap R S ρ))
    (x : TruncatedWittVector p m S)
    (hx : ∀ g, TruncatedWittVector.map (ρ g).toRingHom x = x) :
    ∃ a : TruncatedWittVector p m R, TruncatedWittVector.map (algebraMap R S) a = x := by
  have hcoeff (i : Fin m) : ∀ g, ρ g (x.coeff i) = x.coeff i := by
    intro g
    have h := congrArg (TruncatedWittVector.coeff i) (hx g)
    rw [TruncatedWittVector.map_coeff] at h
    change ρ g (x.coeff i) = x.coeff i at h
    exact h
  choose a ha using fun i : Fin m =>
    (existsUnique_base_of_fixed R S ρ hinj (x.coeff i) (hcoeff i)).exists
  refine ⟨TruncatedWittVector.mk p a, ?_⟩
  apply TruncatedWittVector.ext
  intro i
  rw [TruncatedWittVector.map_coeff, TruncatedWittVector.coeff_mk]
  exact ha i

omit [Fintype G] in
/-- Every cyclic prime-power character of an actual finite faithfully flat
affine torsor comes from a Witt equation over the original base ring. -/
theorem exists_witt_root_of_character [Finite G] (m : ℕ)
    (hTensor : Function.Bijective (tensorMap R S ρ))
    (χ : G →* Multiplicative (ZMod (p ^ m))) :
    ∃ (a : TruncatedWittVector p m R) (β : TruncatedWittVector p m S),
      TruncatedWittVector.map (frobenius S p) β - β =
        TruncatedWittVector.map (algebraMap R S) a ∧
      ∀ g, TruncatedWittVector.map (ρ g).toRingHom β - β =
        ArtinSchreierWittTheory.constantCast p m S (χ g).toAdd := by
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨t, ht⟩ := exists_trace_one R S ρ
    (fun x hx => (existsUnique_base_of_fixed R S ρ hTensor.injective x hx).exists)
    hTensor.surjective
  let c : G → TruncatedWittVector p m S := fun g =>
    ArtinSchreierWittTheory.constantCast p m S (χ g).toAdd
  have hc : ∀ g h : G, c (g * h) = TruncatedWittVector.map (ρ g).toRingHom (c h) + c g := by
    intro g h
    change ArtinSchreierWittTheory.constantCast p m S (χ (g * h)).toAdd =
      TruncatedWittVector.map (ρ g).toRingHom
        (ArtinSchreierWittTheory.constantCast p m S (χ h).toAdd) +
          ArtinSchreierWittTheory.constantCast p m S (χ g).toAdd
    rw [ArtinSchreierWittTheory.constantCast_natural, map_mul]
    change ArtinSchreierWittTheory.constantCast p m S ((χ g).toAdd + (χ h).toAdd) = _
    rw [map_add, add_comm]
  obtain ⟨β, hβ⟩ := wittAdditiveHilbert90_of_trace_one R S ρ p m t ht c hc
  have hfixed : ∀ g, TruncatedWittVector.map (ρ g).toRingHom
      (TruncatedWittVector.map (frobenius S p) β - β) =
        TruncatedWittVector.map (frobenius S p) β - β := by
    intro g
    have hshift : TruncatedWittVector.map (ρ g).toRingHom β = c g + β :=
      (sub_eq_iff_eq_add).mp (hβ g)
    have hcF : TruncatedWittVector.map (frobenius S p) (c g) = c g :=
      ArtinSchreierWittTheory.constantCast_natural p m (frobenius S p) (χ g).toAdd
    rw [map_sub, ← TruncatedWittVector.map_frobenius, hshift, map_add, hcF]
    ring
  obtain ⟨a, ha⟩ := exists_witt_base_of_fixed R S ρ p m hTensor.injective _ hfixed
  exact ⟨a, β, ha.symm, hβ⟩

end GaloisCohomology.FiniteTorsor
