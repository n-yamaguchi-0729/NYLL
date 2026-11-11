/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.Galois.Basic

/-!
# Descent along the original finite Galois coefficient maps

An equivariant isomorphism of finite Galois extensions transports their
actual fixed fields. The descended isomorphism is determined by the literal
coefficient square with the original extension isomorphism. In particular,
descending a reconstructed constant stage does not require distinct boundary
points over the original field.
-/

@[expose] public section

noncomputable section

namespace FieldTheory

universe u₁ u₂ v₁ v₂

variable {K₁ : Type u₁} {K₂ : Type u₂} {L₁ : Type v₁} {L₂ : Type v₂}
  [Field K₁] [Field K₂] [Field L₁] [Field L₂]
  [Algebra K₁ L₁] [Algebra K₂ L₂]
  [FiniteDimensional K₁ L₁] [FiniteDimensional K₂ L₂]
  [IsGalois K₁ L₁] [IsGalois K₂ L₂]
  (Φ : L₁ ≃+* L₂) (θ : Gal(L₁/K₁) ≃* Gal(L₂/K₂))
  (hΦ : ∀ (σ : Gal(L₁/K₁)) (x : L₁), Φ (σ x) = θ σ (Φ x))

include hΦ in
/-- Equivariance identifies the images of the specified base fields by
the Galois fixed-field theorem, with both original coefficient maps intact. -/
theorem galoisEquivariant_mem_base_iff (x : L₁) :
    Φ x ∈ Set.range (algebraMap K₂ L₂) ↔
      x ∈ Set.range (algebraMap K₁ L₁) := by
  constructor
  · intro hx
    apply (IsGalois.mem_range_algebraMap_iff_fixed x).mpr
    intro σ
    apply Φ.injective
    exact (hΦ σ x).trans
      ((IsGalois.mem_range_algebraMap_iff_fixed (Φ x)).mp hx (θ σ))
  · intro hx
    apply (IsGalois.mem_range_algebraMap_iff_fixed (Φ x)).mpr
    intro τ
    obtain ⟨σ, rfl⟩ := θ.surjective τ
    exact (hΦ σ x).symm.trans
      (congrArg Φ ((IsGalois.mem_range_algebraMap_iff_fixed x).mp hx σ))

include hΦ in
/-- The original extension map descends uniquely to the original base
fields. Its value on every original coefficient is the restriction of the
same supplied equivariant map. -/
theorem exists_unique_galoisEquivariantBaseEquiv :
    ∃! φ : K₁ ≃+* K₂,
      ∀ a : K₁, Φ (algebraMap K₁ L₁ a) = algebraMap K₂ L₂ (φ a) := by
  have hex (a : K₁) : ∃ b : K₂,
      algebraMap K₂ L₂ b = Φ (algebraMap K₁ L₁ a) :=
    (galoisEquivariant_mem_base_iff Φ θ hΦ _).mpr ⟨a, rfl⟩
  let m : K₁ → K₂ := fun a => Classical.choose (hex a)
  have hm (a : K₁) : algebraMap K₂ L₂ (m a) = Φ (algebraMap K₁ L₁ a) :=
    Classical.choose_spec (hex a)
  have hinj : Function.Injective m := by
    intro a b hab
    apply (algebraMap K₁ L₁).injective
    apply Φ.injective
    rw [← hm a, ← hm b, hab]
  have hsurj : Function.Surjective m := by
    intro b
    have hb : Φ.symm (algebraMap K₂ L₂ b) ∈ Set.range (algebraMap K₁ L₁) := by
      apply (galoisEquivariant_mem_base_iff Φ θ hΦ _).mp
      rw [RingEquiv.apply_symm_apply]
      exact ⟨b, rfl⟩
    obtain ⟨a, ha⟩ := hb
    refine ⟨a, ?_⟩
    apply (algebraMap K₂ L₂).injective
    rw [hm a, ha, RingEquiv.apply_symm_apply]
  let φ : K₁ ≃+* K₂ :=
    { toEquiv := Equiv.ofBijective m ⟨hinj, hsurj⟩
      map_mul' := fun a b => by
        apply (algebraMap K₂ L₂).injective
        calc
          algebraMap K₂ L₂ (m (a * b)) =
              Φ (algebraMap K₁ L₁ (a * b)) := hm (a * b)
          _ = Φ (algebraMap K₁ L₁ a) * Φ (algebraMap K₁ L₁ b) := by
            rw [map_mul, map_mul]
          _ = algebraMap K₂ L₂ (m a) * algebraMap K₂ L₂ (m b) := by
            rw [hm a, hm b]
          _ = algebraMap K₂ L₂ (m a * m b) := (map_mul _ _ _).symm
      map_add' := fun a b => by
        apply (algebraMap K₂ L₂).injective
        calc
          algebraMap K₂ L₂ (m (a + b)) =
              Φ (algebraMap K₁ L₁ (a + b)) := hm (a + b)
          _ = Φ (algebraMap K₁ L₁ a) + Φ (algebraMap K₁ L₁ b) := by
            rw [map_add, map_add]
          _ = algebraMap K₂ L₂ (m a) + algebraMap K₂ L₂ (m b) := by
            rw [hm a, hm b]
          _ = algebraMap K₂ L₂ (m a + m b) := (map_add _ _ _).symm }
  refine ⟨φ, fun a => (hm a).symm, fun ψ hψ => ?_⟩
  apply RingEquiv.ext
  intro a
  apply (algebraMap K₂ L₂).injective
  exact (hψ a).symm.trans (hm a).symm

include hΦ in
/-- Semilinear equivariant descent retains the specified coefficient maps.
The scalar automorphism of the extension is the scalar automorphism of its
unique descended map between the original fixed fields. -/
theorem exists_unique_galoisEquivariantBaseEquiv_with_coefficients
    {k₁ k₂ : Type*} [Field k₁] [Field k₂]
    [Algebra k₁ K₁] [Algebra k₂ K₂] [Algebra k₁ L₁] [Algebra k₂ L₂]
    [IsScalarTower k₁ K₁ L₁] [IsScalarTower k₂ K₂ L₂]
    (τ : k₁ ≃+* k₂)
    (hcoeff : ∀ r : k₁, Φ (algebraMap k₁ L₁ r) = algebraMap k₂ L₂ (τ r)) :
    ∃! φ : K₁ ≃+* K₂,
      (∀ a : K₁, Φ (algebraMap K₁ L₁ a) = algebraMap K₂ L₂ (φ a)) ∧
      ∀ r : k₁, φ (algebraMap k₁ K₁ r) = algebraMap k₂ K₂ (τ r) := by
  obtain ⟨φ, hφ, huniq⟩ := exists_unique_galoisEquivariantBaseEquiv Φ θ hΦ
  refine ⟨φ, ⟨hφ, ?_⟩, fun ψ hψ => huniq ψ hψ.1⟩
  intro r
  apply (algebraMap K₂ L₂).injective
  calc
    algebraMap K₂ L₂ (φ (algebraMap k₁ K₁ r)) =
        Φ (algebraMap K₁ L₁ (algebraMap k₁ K₁ r)) := (hφ _).symm
    _ = Φ (algebraMap k₁ L₁ r) :=
      congrArg Φ (IsScalarTower.algebraMap_apply k₁ K₁ L₁ r).symm
    _ = algebraMap k₂ L₂ (τ r) := hcoeff r
    _ = algebraMap K₂ L₂ (algebraMap k₂ K₂ (τ r)) :=
      IsScalarTower.algebraMap_apply k₂ K₂ L₂ (τ r)

/-- Equivariant descent over a fixed coefficient field produces an algebra
isomorphism, uniquely determined by the original extension square. -/
theorem exists_unique_galoisEquivariantBaseAlgEquiv
    {k : Type*} [Field k] [Algebra k K₁] [Algebra k K₂]
    [Algebra k L₁] [Algebra k L₂]
    [IsScalarTower k K₁ L₁] [IsScalarTower k K₂ L₂]
    (e : L₁ ≃ₐ[k] L₂)
    (he : ∀ (σ : Gal(L₁/K₁)) (x : L₁), e (σ x) = θ σ (e x)) :
    ∃! f : K₁ ≃ₐ[k] K₂,
      ∀ a : K₁, e (algebraMap K₁ L₁ a) = algebraMap K₂ L₂ (f a) := by
  obtain ⟨φ, hφ, huniq⟩ :=
    exists_unique_galoisEquivariantBaseEquiv_with_coefficients e.toRingEquiv θ he
      (RingEquiv.refl k) e.commutes
  let f : K₁ ≃ₐ[k] K₂ := AlgEquiv.ofRingEquiv (f := φ) hφ.2
  refine ⟨f, hφ.1, ?_⟩
  intro g hg
  apply AlgEquiv.toRingEquiv_injective
  exact huniq g.toRingEquiv ⟨hg, g.commutes⟩

end FieldTheory
