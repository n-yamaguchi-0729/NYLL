/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.AffineArtinSchreierCover
public import Nyll.GaloisCohomology.FieldTheory.WittCoefficientFrobenius
public import Nyll.GaloisCohomology.ArtinSchreier.WittCharacters
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Finite étale root extensions for every Witt coefficient

At each Witt length, adjoin one actual Artin–Schreier root of the constant
coefficient. Subtract its Teichmüller difference and use the actual
Verschiebung tail for the remaining equation. Iteration produces a finite
étale faithfully flat algebra over the original ring, with a Witt root.
-/

@[expose] public section

noncomputable section

namespace EtaleFundamentalGroups.Cohomology

universe u

open WittVector

/-- Every finite truncation of a Witt equation acquires an actual root in
a finite étale faithfully flat extension of its original coefficient ring. -/
theorem exists_finiteEtale_wittRoot_extension
    (p : ℕ) [Fact p.Prime] (n : ℕ) (R : Type u)
    [CommRing R] [Nontrivial R] [CharP R p] (a : WittVector p R) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (_ : CharP S p)
      (_ : Module.Finite R S) (_ : Algebra.Etale R S) (_ : Module.FaithfullyFlat R S)
      (β : WittVector p S),
      truncate n (WittVector.map (frobenius S p) β - β) =
        TruncatedWittVector.map (algebraMap R S) (truncate n a) := by
  induction n generalizing R with
  | zero =>
    refine ⟨R, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, 0, ?_⟩
    apply TruncatedWittVector.ext
    exact fun i => Fin.elim0 i
  | succ n ih =>
    let S := ArtinSchreierAlgebra R p (a.coeff 0)
    have : Module.Finite R S := artinSchreierAlgebra_finite R p (a.coeff 0)
    have : Algebra.Etale R S := artinSchreierAlgebra_etale R p (a.coeff 0)
    have : Module.FaithfullyFlat R S := artinSchreierAlgebra_faithfullyFlat R p (a.coeff 0)
    have : CharP S p := artinSchreierAlgebra_charP R p (a.coeff 0)
    have : Nontrivial S := CharP.nontrivial_of_char_ne_one (Fact.out : p.Prime).ne_one
    let b : S := AdjoinRoot.root _
    have hb : b ^ p - b = algebraMap R S (a.coeff 0) :=
      artinSchreierAlgebra_root R p (a.coeff 0)
    let y : WittVector p S := WittVector.map (algebraMap R S) a
    let t : WittVector p S := teichmuller p b
    let dS : WittVector p S →+ WittVector p S :=
      (WittVector.map (frobenius S p)).toAddMonoidHom - AddMonoidHom.id _
    have hz0 : (y - dS t).coeff 0 = 0 := by
      change constantCoeff (y - (WittVector.map (frobenius S p) t - t)) = 0
      rw [map_sub, map_sub]
      change algebraMap R S (a.coeff 0) - (b ^ p - b) = 0
      rw [hb, sub_self]
    obtain ⟨z, hz⟩ := exists_verschiebung_eq_of_coeff_zero (y - dS t) hz0
    have hy : y = dS t + verschiebung z := by
      rw [hz, add_sub_cancel]
    obtain ⟨T, ringT, algST, charT, finiteST, etaleST, flatST, x, hx⟩ := ih S z
    let : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
    have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
    have : Module.Finite R T := Module.Finite.trans S T
    have : Algebra.Etale R T := Algebra.Etale.comp R S T
    have : Module.FaithfullyFlat R T := Module.FaithfullyFlat.trans R S T
    let tT : WittVector p T := WittVector.map (algebraMap S T) t
    let dT : WittVector p T →+ WittVector p T :=
      (WittVector.map (frobenius T p)).toAddMonoidHom - AddMonoidHom.id _
    have hmapd (w : WittVector p S) :
        WittVector.map (algebraMap S T) (dS w) =
          dT (WittVector.map (algebraMap S T) w) := by
      change WittVector.map (algebraMap S T) (WittVector.map (frobenius S p) w - w) =
        WittVector.map (frobenius T p) (WittVector.map (algebraMap S T) w) -
          WittVector.map (algebraMap S T) w
      rw [map_sub]
      congr 1
      apply WittVector.ext
      intro i
      change algebraMap S T ((w.coeff i) ^ p) = (algebraMap S T (w.coeff i)) ^ p
      exact map_pow (algebraMap S T) (w.coeff i) p
    have hyT : WittVector.map (algebraMap R T) a =
        dT tT + verschiebung (WittVector.map (algebraMap S T) z) := by
      calc
        WittVector.map (algebraMap R T) a = WittVector.map (algebraMap S T) y := by
          apply WittVector.ext
          exact fun _ => rfl
        _ = dT tT + verschiebung (WittVector.map (algebraMap S T) z) := by
          rw [hy, map_add, hmapd, map_verschiebung]
    have hx' : truncate n (dT x) = truncate n (WittVector.map (algebraMap S T) z) := by
      rw [TruncatedWittVector.map_wittVector_truncate] at hx
      exact hx
    have hdV : dT (verschiebung x) = verschiebung (dT x) := by
      change WittVector.map (frobenius T p) (verschiebung x) - verschiebung x =
        verschiebung (WittVector.map (frobenius T p) x - x)
      rw [map_verschiebung, map_sub]
    refine ⟨T, ringT, inferInstance, charT, inferInstance, inferInstance,
      inferInstance, tT + verschiebung x, ?_⟩
    change truncate (n + 1) (dT (tT + verschiebung x)) = _
    calc
      truncate (n + 1) (dT (tT + verschiebung x)) =
          truncate (n + 1) (dT tT + verschiebung (dT x)) := by rw [map_add, hdV]
      _ = truncate (n + 1)
          (dT tT + verschiebung (WittVector.map (algebraMap S T) z)) := by
        rw [map_add, map_add]
        exact congrArg (fun v => truncate (n + 1) (dT tT) + v)
          (truncate_verschiebung_eq_of_truncate_eq hx')
      _ = truncate (n + 1) (WittVector.map (algebraMap R T) a) :=
        congrArg (truncate (n + 1)) hyT.symm
      _ = TruncatedWittVector.map (algebraMap R T) (truncate (n + 1) a) :=
        (TruncatedWittVector.map_wittVector_truncate _ _).symm

/-- An arbitrary finite Witt coefficient has a root over a finite étale
faithfully flat algebra, without changing the original base ring. -/
theorem exists_finiteEtale_truncatedWittRoot_extension
    (p : ℕ) [Fact p.Prime] (n : ℕ) (R : Type u)
    [CommRing R] [Nontrivial R] [CharP R p] (a : TruncatedWittVector p n R) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (_ : CharP S p)
      (_ : Module.Finite R S) (_ : Algebra.Etale R S) (_ : Module.FaithfullyFlat R S)
      (β : TruncatedWittVector p n S),
      TruncatedWittVector.map (frobenius S p) β - β =
        TruncatedWittVector.map (algebraMap R S) a := by
  obtain ⟨a', rfl⟩ := WittVector.truncate_surjective p n R a
  obtain ⟨S, ringS, algS, charS, finiteS, etaleS, flatS, β, hβ⟩ :=
    exists_finiteEtale_wittRoot_extension p n R a'
  refine ⟨S, ringS, algS, charS, finiteS, etaleS, flatS, truncate n β, ?_⟩
  rw [TruncatedWittVector.map_wittVector_truncate, ← map_sub]
  exact hβ

end EtaleFundamentalGroups.Cohomology
