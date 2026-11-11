/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_local_coboundary_of_smallExtension_of_monogenic_fibre.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_bounded_two_cochain_of_local_coboundaries.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_wittVector_lift_of_normalFormOrder.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_mul_eq_hochschild_coboundary_of_discr_ne_zero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Ring.RingNF

/-!
# Coordinate algebras of commutative multiplication tables

The carrier, ring operations, scalar action and coordinate basis share one implementation.
Coordinate composition permits distinct inner and outer multiplication tables.
-/

@[expose] public section

namespace TableAlgebra

noncomputable section

/-- Structure constants of a commutative unital multiplication table. -/
structure Table (R : Type*) [CommRing R] (N : ℕ) where
  /-- The structure constants of multiplication. -/
  γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R
  /-- The first basis vector acts as the multiplicative unit. -/
  unit : ∀ j k, γ 0 j k = if j = k then 1 else 0
  /-- The structure constants are symmetric in the two factors. -/
  comm : ∀ i j k, γ i j k = γ j i k
  /-- The structure constants satisfy associativity. -/
  assoc : ∀ i j l m, ∑ k, γ i j k * γ k l m = ∑ k, γ j l k * γ i k m

variable {R : Type*} [CommRing R] {N : ℕ}

/-- The product of coordinate vectors determined by structure constants. -/
def cst (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (x y : Fin (N + 1) → R) :
    Fin (N + 1) → R :=
  fun m => ∑ i, ∑ j, x i * y j * γ i j m

theorem cst_apply (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (x y : Fin (N + 1) → R)
    (m : Fin (N + 1)) : cst γ x y m = ∑ i, ∑ j, x i * y j * γ i j m := rfl

theorem sum3_rot (f : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) :
    ∑ q, ∑ l, ∑ t, f q l t = ∑ l, ∑ t, ∑ q, f q l t := by
  calc ∑ q, ∑ l, ∑ t, f q l t = ∑ l, ∑ q, ∑ t, f q l t := Finset.sum_comm
    _ = ∑ l, ∑ t, ∑ q, f q l t := Finset.sum_congr rfl fun l _ => Finset.sum_comm

theorem sum4_rot (f : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) :
    ∑ q, ∑ t, ∑ k, ∑ l, f q t k l = ∑ k, ∑ l, ∑ t, ∑ q, f q t k l := by
  calc ∑ q, ∑ t, ∑ k, ∑ l, f q t k l = ∑ q, ∑ k, ∑ t, ∑ l, f q t k l :=
        Finset.sum_congr rfl fun q _ => Finset.sum_comm
    _ = ∑ q, ∑ k, ∑ l, ∑ t, f q t k l :=
        Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k, ∑ q, ∑ l, ∑ t, f q t k l := Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ q, ∑ t, f q t k l := Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ t, ∑ q, f q t k l :=
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => Finset.sum_comm

theorem cst_cst_left (γo γi : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R)
    (a b c : Fin (N + 1) → R) (s : Fin (N + 1)) :
    cst γo (cst γi a b) c s = ∑ k, ∑ l, ∑ t, a k * b l * c t * ∑ q, γi k l q * γo q t s := by
  simp only [cst, Finset.sum_mul, Finset.mul_sum]
  rw [sum4_rot]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
    Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun q _ => ?_
  ring

theorem cst_cst_right (γo γi : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R)
    (a b c : Fin (N + 1) → R) (s : Fin (N + 1)) :
    cst γo a (cst γi b c) s = ∑ k, ∑ l, ∑ t, a k * b l * c t * ∑ q, γi l t q * γo k q s := by
  simp only [cst, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sum3_rot]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun t _ =>
    Finset.sum_congr rfl fun q _ => ?_
  ring

theorem cst_comm_of (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R)
    (hc : ∀ i j k, γ i j k = γ j i k) (a b : Fin (N + 1) → R) : cst γ a b = cst γ b a := by
  funext m
  rw [cst_apply, cst_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hc j i m]; ring

theorem cst_add_left (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (a a' b : Fin (N + 1) → R) :
    cst γ (a + a') b = cst γ a b + cst γ a' b := by
  funext m
  simp only [cst, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem cst_add_right (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (a b b' : Fin (N + 1) → R) :
    cst γ a (b + b') = cst γ a b + cst γ a b' := by
  funext m
  simp only [cst, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem cst_smul_left (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (z : R)
    (a b : Fin (N + 1) → R) : cst γ (z • a) b = z • cst γ a b := by
  funext m
  simp only [cst, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem cst_zero_left (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (b : Fin (N + 1) → R) :
    cst γ 0 b = 0 := by
  funext m
  simp only [cst, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

theorem cst_single_left (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (i : Fin (N + 1))
    (y : Fin (N + 1) → R) (m : Fin (N + 1)) :
    cst γ (Pi.single i 1) y m = ∑ q, y q * γ i q m := by
  rw [cst_apply, Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same, one_mul]
  · intro b _ hb; simp only [Pi.single_eq_of_ne hb, zero_mul, Finset.sum_const_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem cst_single_single (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (i j : Fin (N + 1)) :
    cst γ (Pi.single i 1) (Pi.single j 1) = fun m => γ i j m := by
  funext m
  rw [cst_apply, Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp only [Pi.single_eq_same, one_mul]
  · intro b _ hb; rw [Pi.single_eq_of_ne hb, mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ j) h
  · intro b _ hb; simp only [Pi.single_eq_of_ne hb, zero_mul, Finset.sum_const_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem cst_unit_left (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R)
    (h1 : ∀ j k, γ 0 j k = if j = k then 1 else 0) (b : Fin (N + 1) → R) :
    cst γ (Pi.single 0 1) b = b := by
  funext m
  rw [cst_apply, Finset.sum_eq_single 0]
  · simp only [Pi.single_eq_same, one_mul, h1]
    rw [Finset.sum_eq_single m]
    · simp only [ite_true, mul_one]
    · intro j _ hj; rw [ite_eq_right hj, mul_zero]
    · intro h; exact absurd (Finset.mem_univ m) h
  · intro i _ hi; simp only [Pi.single_eq_of_ne hi, zero_mul, Finset.sum_const_zero]
  · intro h; exact absurd (Finset.mem_univ (0 : Fin (N + 1))) h

/-- The algebra with the given multiplication table. -/
structure TAlg (T : Table R N) where
  /-- The coordinate vector of an element. -/
  coord : Fin (N + 1) → R

namespace TAlg

variable (T : Table R N)

@[scoped ext] theorem ext {x y : TAlg T} (h : x.coord = y.coord) : x = y := by
  cases x; cases y; congr

/-- The coordinate equivalence of the table algebra. -/
def equiv : TAlg T ≃ (Fin (N + 1) → R) where
  toFun := coord
  invFun := TAlg.mk
  left_inv _ := rfl
  right_inv _ := rfl

scoped instance instAddCommGroup : AddCommGroup (TAlg T) := (equiv T).addCommGroup

/-- The additive coordinate equivalence of the table algebra. -/
def addEquiv : TAlg T ≃+ (Fin (N + 1) → R) where
  toEquiv := equiv T
  map_add' _ _ := rfl

scoped instance instModule : Module R (TAlg T) := (addEquiv T).module R

@[scoped simp] theorem coord_add (x y : TAlg T) : (x + y).coord = x.coord + y.coord := rfl
@[scoped simp] theorem coord_zero : (0 : TAlg T).coord = 0 := rfl
@[scoped simp] theorem coord_neg (x : TAlg T) : (-x).coord = -x.coord := rfl
@[scoped simp] theorem coord_sub (x y : TAlg T) : (x - y).coord = x.coord - y.coord := rfl
@[scoped simp] theorem coord_smul (z : R) (x : TAlg T) : (z • x).coord = z • x.coord := rfl
@[scoped simp] theorem coord_mk (v : Fin (N + 1) → R) : (TAlg.mk v : TAlg T).coord = v := rfl

/-- The linear coordinate equivalence of the table algebra. -/
def linearEquiv : TAlg T ≃ₗ[R] (Fin (N + 1) → R) :=
  { equiv T with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

@[scoped simp] theorem linearEquiv_apply (x : TAlg T) : linearEquiv T x = x.coord := rfl
@[scoped simp] theorem linearEquiv_symm_apply (v : Fin (N + 1) → R) : (linearEquiv T).symm v =
  TAlg.mk v :=
  rfl

theorem coord_sum {ι : Type*} (s : Finset ι) (f : ι → TAlg T) :
    (∑ i ∈ s, f i).coord = ∑ i ∈ s, (f i).coord := by
  change linearEquiv T (∑ i ∈ s, f i) = ∑ i ∈ s, linearEquiv T (f i)
  exact map_sum _ _ _

scoped instance instMul : Mul (TAlg T) := ⟨fun x y => TAlg.mk (cst T.γ x.coord y.coord)⟩

scoped instance instOne : One (TAlg T) := ⟨TAlg.mk (Pi.single 0 1)⟩

@[scoped simp] theorem coord_mul (x y : TAlg T) : (x * y).coord = cst T.γ x.coord y.coord := rfl
@[scoped simp] theorem coord_one : (1 : TAlg T).coord = Pi.single 0 1 := rfl

theorem mul_comm' (x y : TAlg T) : x * y = y * x := by
  ext1; simp only [coord_mul]; exact cst_comm_of T.γ T.comm _ _

theorem mul_assoc' (x y z : TAlg T) : x * y * z = x * (y * z) := by
  ext1
  simp only [coord_mul]
  funext s
  rw [cst_cst_left, cst_cst_right]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
    Finset.sum_congr rfl fun t _ => ?_
  rw [T.assoc k l t s]

theorem one_mul' (x : TAlg T) : 1 * x = x := by
  ext1; simp only [coord_mul, coord_one]; exact cst_unit_left T.γ T.unit _

scoped instance instCommRing : CommRing (TAlg T) where
  __ := (inferInstance : AddCommGroup (TAlg T))
  mul := (· * ·)
  one := 1
  mul_assoc := mul_assoc' T
  one_mul := one_mul' T
  mul_one x := by rw [mul_comm']; exact one_mul' T x
  zero_mul x := by ext1; simp only [coord_mul, coord_zero]; exact cst_zero_left _ _
  mul_zero x := by rw [mul_comm']; ext1; simp only [coord_mul, coord_zero]; exact cst_zero_left _ _
  left_distrib x y z := by ext1; simp only [coord_mul, coord_add]; exact cst_add_right _ _ _ _
  right_distrib x y z := by ext1; simp only [coord_mul, coord_add]; exact cst_add_left _ _ _ _
  mul_comm := mul_comm' T

theorem smul_mul_assoc' (z : R) (x y : TAlg T) : (z • x) * y = z • (x * y) := by
  ext1; simp only [coord_mul, coord_smul]; exact cst_smul_left _ _ _ _

scoped instance instAlgebra : Algebra R (TAlg T) :=
  Algebra.ofModule (smul_mul_assoc' T) fun z x y => by
    rw [mul_comm', smul_mul_assoc', mul_comm']

/-- The coordinate basis of the table algebra. -/
def basis : Module.Basis (Fin (N + 1)) R (TAlg T) := Module.Basis.ofEquivFun (linearEquiv T)

theorem basis_apply (i : Fin (N + 1)) : basis T i = TAlg.mk (Pi.single i 1) := by
  rw [basis, Module.Basis.coe_ofEquivFun]; rfl

theorem coord_basis (i : Fin (N + 1)) : (basis T i).coord = Pi.single i 1 := by
  rw [basis_apply]

theorem basis_repr_apply (x : TAlg T) (k : Fin (N + 1)) : (basis T).repr x k = x.coord k := by
  rw [basis, Module.Basis.ofEquivFun_repr_apply]; rfl

theorem basis_zero : basis T 0 = 1 := by
  ext1; rw [coord_basis, coord_one]

theorem basis_mul_basis_coord (i j : Fin (N + 1)) :
    (basis T i * basis T j).coord = fun m => T.γ i j m := by
  rw [coord_mul, coord_basis, coord_basis, cst_single_single]

theorem repr_basis_mul_basis (i j k : Fin (N + 1)) :
    (basis T).repr (basis T i * basis T j) k = T.γ i j k := by
  rw [basis_repr_apply, basis_mul_basis_coord]

theorem algebraMap_coord (f : R) : (algebraMap R (TAlg T) f).coord = Pi.single 0 f := by
  rw [Algebra.algebraMap_eq_smul_one, coord_smul, coord_one, ← Pi.single_smul, smul_eq_mul, mul_one]

theorem eq_sum_coord_smul_basis (x : TAlg T) : x = ∑ i, x.coord i • basis T i := by
  conv_lhs => rw [← (basis T).sum_repr x]
  simp only [basis_repr_apply]

/-- The coordinate basis vector with the specified index. -/
def e (i : Fin (N + 1)) : TAlg T := TAlg.mk (Pi.single i 1)

@[scoped simp] theorem coord_e (i : Fin (N + 1)) : (e T i).coord = Pi.single i 1 := rfl

end TAlg

end

end TableAlgebra
