/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.Basic
public import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.Centered
public import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.CenteredTransport
public import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.Counting
public import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.Dedekind
public import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.DegreeOne
public import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.Infinity
public import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.InseparableCounting
public import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.IntegralClosure
public import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.PrimesOver
public import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.Transport

/-!
# Prime divisors of function fields

This aggregate exposes centered prime divisors, degree and counting comparisons,
integral-closure primes, divisors at infinity, and transport across function-field maps.
-/

/- Canonical aggregate for SchemeTheory.FunctionFields.PrimeDivisors. -/
