---
layout: post
title: "Problem #3 Solution"
---

*[Problem #3 is here](https://coq-math-problems.github.io/Problem3/)*

*[Problem #3 Solution File](https://github.com/Coq-Math-Problems/Problems/blob/master/P3/P3_solution.v)*

The key lemma is that we can use Dedekind-finiteness of `X` to find solutions for `x` in equations of the form `a * x = b` and `x * a = b`.  First, note that left and right multiplication of a given element is injective.  This follows immediately from left- and right-cancellativity of `*`.  We can then apply the Dedekind-finiteness assumption to show left and right multiplication are surjective.  This of course is exactly the statement that all equations `a * x = b` and `x * a = b` have solutions.  We package this into two lemmas:

`Lemma r_eq_solve : forall a b, {x : X & a * x = b}.`

`Lemma l_eq_solve : forall a b, {x : X & x * a = b}.`

(note that we can't use the `Prop` existential quantifier, since we will need to use these facts to construct the identity and inverse)

At this stage, we have only one element `x0` and a means of constructing solutions to these basic equations.  Certainly, we know that the identity will uniquely solve the equation `x * x0 = x0`, so we will take this element as our identity `e`.  We know then that `e * x0 = x0`, but how can we show this for *any* `x` and not just `x0`?  This follows from a couple of rewrites.  First, let `y` be such that `x = x0 * y` (by `r_eq_solve`).  We then have that

` e * x = e * (x0 * y) = (e * x0) * y = x0 * y = x`.

Thus, `e` is indeed a left identity.  What about right?  Using right-cancellativity, to show that `x * e = x`, it suffices to show that `(x * e) * e = x * e`.  This follows immediately from the fact that `e` is a left identity:

` (x * e) * e = x * (e * e) = x * e`.

(note that the choice of `e` as the 'cancelling' element on the right is entirely arbitrary)

With `e` defined at its properties now established, we move onto defining the inverse.  We take `inv x` to be element given by `l_eq_solve` such that `inv x * x = e`.  Thus, the left inverse property is automatic.  To establish the right inverse property, we again use right-cancellativity.  To show that `x * inv x = e`, it suffices to show that `(x * inv x) * x = e * x`:

 ` (x * inv x) * x = x * (inv x * x) = x * e = x = e * x`.
