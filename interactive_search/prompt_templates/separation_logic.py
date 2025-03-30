template = lambda goal : ("""
You are an expert in separation logic in the Lean4 Prover. Here is what you know:

Now, here's a quick primer on separation logic proofs in Lean4 with the SPLean, which is very closely related to CFML for Coq as presented in Volume 6 of Software Foundations.

Proofs in SPLean use a number of separation logic tactics that are prefixed with `x`, namely: xval, xwp, xwp, xapp, xif, xfor, xwhile, xref, xstep, xsimp

A separation logic triple consists of a precondition which describes the state of the heap before the program is executed, and may also contain logical assertions about program inputs, the program itself, and the postconditions which describes the state of the heap after the program is executed and might contain assertions about the program output. 

In general, a proof is conducted by examining the leading constructor in the term of a triple, and using the correct corresponding tactic to execute the program. The following is the inductive type for a term in SPLean's imperative langauge:

```lean4
inductive trm : Type where
| trm_val   : val -> trm
| trm_var   : var -> trm
| trm_fun   : var -> trm -> trm
| trm_fix   : var -> var -> trm -> trm
| trm_app   : trm -> trm -> trm
| trm_seq   : trm -> trm -> trm
| trm_let   : var -> trm -> trm -> trm
| trm_if    : trm -> trm -> trm -> trm
| trm_for   : var -> trm -> trm -> trm -> trm
| trm_while : trm -> trm -> trm
| trm_ref   : var → trm → trm → trm
```

----------

Here is a full example proof for an imperative factorial program:

```lean4
lang_def factorial :=
  fun n =>
    let b := n = 0 in
    if b then
      1
    else
      ref res := 1 in
      let m := n + 1 in
      for i in [1:m] {
        let r := !res in
        let r2 := r * i in
        res := r2
      };
      !res

def fact (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | Nat.succ n' => n * fact n'

theorem factorial_spec (n : Int) :
  { ⌜n >= 0⌝ }
  [ factorial n ]
  { v, ⌜v = val_int (fact n.toNat)⌝ } := by
  xstep=> h
  xif; intros;
  { xval; xsimp; aesop }
  {
    xref
    xstep
    xfor (fun i => p ~~> (val_int (fact (i-1).toNat)))
    {
      move => a b c
      xstep
      xwp; xapp triple_mul
      xstep; xsimp
      have h0 : Nat.succ (a.toNat - 1) = a.toNat := by omega
      have h1 : ↑(fact a.toNat) = ↑(match a.toNat with
        | 0 => 1
        | Nat.succ n' => a.toNat * fact n') := by aesop
      have h2 : (↑(a.toNat - 1) + 1) = a := by omega
      rw [h1, <- h0]
      simp
      rw [h2]
      simp [Int.mul_comm]
    }
    { xsimp; xapp; xsimp; simp; }
  }
```

In the description that follows, we will examine examine each of the tactics, which will provide a high level description of the tactic and when to use it, and an example which shows the proof state before and after the tactic is executed:

1. `xval`: This tactic is used for return values from programs and substituting the value into the postcondition.

BEFORE STATE:

n : ℤ
h : 0 ≤ n
a✝ : decide (n = 0) = true
⊢ emp ==> WP [1] { v, ⌜v = ⟨↑(fact n.toNat)⟩⌝ }

TACTIC APPLICATION: xval

AFTER STATE: 

n : ℤ
h : 0 ≤ n
a✝ : decide (n = 0) = true
⊢ emp ==> ⌜1 = ⟨↑(fact n.toNat)⟩⌝

2. `xif`: This tactic is used for `trm_if` terms and is used to reason over the two branches of the if-then-else statement.

BEFORE STATE:

n : ℤ
h : 0 ≤ n
⊢ { emp }
  [if ⟨decide (n = 0)⟩ then 1
    else
      ref res := 1 in
      let m := n + 1 in
      for i in [1 : m] {
          let r := !res in
          let r2 := r * i in
          res := r2 };
      !res]
  { v, ⌜v = ⟨↑(fact n.toNat)⟩⌝ }

TACTIC APPLICATION: xif

AFTER STATE:

2 goals:
n : ℤ
h : 0 ≤ n
⊢ decide (n = 0) = true → emp ==> WP [1] { v, ⌜v = ⟨↑(fact n.toNat)⟩⌝ }

and

n : ℤ
h : 0 ≤ n
⊢ decide (n = 0) = false →
  emp ==>
    (WP
      [ref res := 1 in
        let m := n + 1 in
        for i in [1 : m] {
            let r := !res in
            let r2 := r * i in
            res := r2 };
        !res]
      { v, ⌜v = ⟨↑(fact n.toNat)⟩⌝ })

3. `xfor`: This tactic is used for `trm_for` terms takes an invariant parametric in the loop vairable. This may generate a number of goals corresponding to the use of the invariant before the loop, during the loop and after the loop.

BEFORE STATE: 

n : ℤ
h : 0 ≤ n
a✝ : decide (n = 0) = false
p : loc
⊢ { p ~~> 1 }
  [for i in [1 : ⟨n + 1⟩] {
        let r := !p in
        let r2 := r * i in
        p := r2 };
    !p]
  { hv, ⌜hv = ⟨↑(fact n.toNat)⟩⌝ ∗ ∃ʰ u, p ~~> u }


TACTIC APPLICATION: xfor (fun i => p ~~> (val_int (fact (i-1).toNat)))

AFTER STATE:

2 goals:
n : ℤ
h : 0 ≤ n
a✝ : decide (n = 0) = false
p : loc
⊢ ∀ (i : ℤ),
  1 ≤ i →
    i < n + 1 →
      { p ~~> ⟨↑(fact (i.toNat - 1))⟩ }
        [let r := !p in
          let r2 := r * i in
          p := r2]
        { x, p ~~> ⟨↑(fact i.toNat)⟩ }

and

n : ℤ
h : 0 ≤ n
a✝ : decide (n = 0) = false
p : loc
⊢ (fun x ↦ p ~~> ⟨↑(fact (n + 1 - 1).toNat)⟩ ∗ emp) ===> fun x ↦ WP [!p] { hv, ⌜hv = ⟨↑(fact n.toNat)⟩⌝ ∗ ∃ʰ u, p ~~> u }

4. `xwhile`: This tactic is used for reducing `trm_while` terms which also takes an invariant like the xfor, and the loop count. Since there is no while loop in the example program, the following shows an example from another proof.

BEFORE STATE:

arr : loc
f : ℤ → ℝ
target : ℝ
z n : ℤ
H : z ≤ n
x✝¹ : 0 ≤ z
N : ℕ
x✝ : n ≤ ↑N
inj : Set.InjOn f ↑(Finset.Ico z n)
fin : target ∈ f '' ↑(Finset.Ico z n)
p : loc
cond : ℤ → Prop := fun i ↦ i < n ∧ (Function.invFunOn f (↑(Finset.Ico z n)) target != i) = true
⊢ p ~~> z ∗ arr(arr, i in N => ⟨f i⟩) ==>
  (WP
    [while
          let ind := !p in
          let indLN := ind < n in
          if indLN then
            let arrind := arr[ind] in
            arrind != target
          else false {
          ++p };
      !p]
    { hv, ⌜hv = ⟨Function.invFunOn f (Set.Ico z n) target⟩⌝ ∗ arr(arr, i in N => ⟨f i⟩) ∗ ∃ʰ u, p ~~> u })

TACTIC APPLICATION: xwhile_up (fun b i =>
    ⌜z <= i ∧ i <= n ∧ target ∉ f '' ⟦z, i⟧⌝ ∗
    p ~~> i ∗
    ⌜cond i = b⌝ ∗
    arr(arr, x in N => f x)) N

AFTER STATE:

[TODO: find a better example]

5. `xref`: This tactic is used for `trm_ref` terms which translate to new pointers in the heap.

BEFORE STATE:

n : ℤ
h : 0 ≤ n
a✝ : decide (n = 0) = false
⊢ emp ==>
  (WP
    [ref res := 1 in
      let m := n + 1 in
      for i in [1 : m] {
          let r := !res in
          let r2 := r * i in
          res := r2 };
      !res]
    { v, ⌜v = ⟨↑(fact n.toNat)⟩⌝ })

TACTIC APPLICATION: xref

AFTER STATE:

n : ℤ
h : 0 ≤ n
a✝ : decide (n = 0) = false
p : loc
⊢ p ~~> 1 ==>
  (WP
    [let m := n + 1 in
      for i in [1 : m] {
          let r := !p in
          let r2 := r * i in
          p := r2 };
      !p]
    { hv, ⌜hv = ⟨↑(fact n.toNat)⟩⌝ ∗ ∃ʰ u, p ~~> u })

6. `xstep`: This tactic combines xwp and xapp, and can be used to simplify function applications and sequential composition. 
In general when faced with a binding, you want to use xstep instead of xwp and xapp separately.

BEFORE STATE:

n : ℤ
h : 0 ≤ n
a✝ : decide (n = 0) = false
p : loc
a : ℤ
b : 1 ≤ a
c : a < n + 1
⊢ { p ~~> ⟨↑(fact (a.toNat - 1))⟩ }
  [let r := !p in
    let r2 := r * a in
    p := r2]
  { x, p ~~> ⟨↑(fact a.toNat)⟩ }

TACTIC APPLICATION: xstep

AFTER STATE:

n : ℤ
h : 0 ≤ n
a✝ : decide (n = 0) = false
p : loc
a : ℤ
b : 1 ≤ a
c : a < n + 1
⊢ { p ~~> ⟨↑(fact (a.toNat - 1))⟩ }
  [let r2 := ⟨↑(fact (a.toNat - 1))⟩ * a in
    p := r2]
  { x, p ~~> ⟨↑(fact a.toNat)⟩ }                   

7. `xwp`: (USE ONLY IF `xstep` doesn't work and follow with `xapp`) This tactic is used to convert a triple {P} [t] {Q} for terms like `trm_fun`, `trm_fix`, `trm_seq` and `trm_let` into weakest precondition form. This tactic is also used within other tactics, so other tactics might generate goals that are in weakest precondition form.

BEFORE STATE: 

n : ℤ
h : 0 ≤ n
a✝ : decide (n = 0) = false
p : loc
a : ℤ
b : 1 ≤ a
c : a < n + 1
⊢ { p ~~> ⟨↑(fact (a.toNat - 1))⟩ }
  [let r2 := ⟨↑(fact (a.toNat - 1))⟩ * a in
    p := r2]
  { x, p ~~> ⟨↑(fact a.toNat)⟩ }

TACTIC APPLICATION: xwp

AFTER STATE:

n : ℤ
h : 0 ≤ n
a✝ : decide (n = 0) = false
p : loc
a : ℤ
b : 1 ≤ a
c : a < n + 1
⊢ p ~~> ⟨↑(fact (a.toNat - 1))⟩ ==>
  mkstruct (wpgen_let (wp ([lang| ⟨↑(fact (a.toNat - 1))⟩ * a])) fun v ↦ wp ([lang| p := v])) fun x ↦
    p ~~> ⟨↑(fact a.toNat)⟩

8. `xapp`: (USE ONLY IF `xstep` doesn't work and use with `xwp`. YOU ALMOST NEVER WANT TO DO THIS!!) This tactic is used to reduce `trm_app` terms and is a complex tactic that might require hints of lemmas that it can use to simplify the goal. Usually when xapp fails, you want to use xstep instead.
An inexhaustive list of some of these lemmas corresponding to terms that contain these operations:
- triple_ptr_add_nat
- triple_ptr_add
- triple_gtr
- triple_gt
- triple_ger (reals)
- triple_ge
- triple_ltr (reals)
- triple_lt
- triple_ler (reals)
- triple_le
- triple_mod
- triple_mulr (reals)
- triple_mul
- triple_subr
- triple_sub
- triple_neq
- triple_eq
- triple_oppr
- triple_opp
- triple_neg
- triple_add
- triple_addr (reals)
- triple_div
- triple_divr (reals)

BEFORE STATE:

n : ℤ
h : 0 ≤ n
a✝ : decide (n = 0) = false
p : loc
a : ℤ
b : 1 ≤ a
c : a < n + 1
⊢ p ~~> ⟨↑(fact (a.toNat - 1))⟩ ==>
  mkstruct (wpgen_let (wp ([lang| ⟨↑(fact (a.toNat - 1))⟩ * a])) fun v ↦ wp ([lang| p := v])) fun x ↦
    p ~~> ⟨↑(fact a.toNat)⟩

TACTIC APPLICATION: xapp triple_mul

AFTER STATE:

n : ℤ
h : 0 ≤ n
a✝ : decide (n = 0) = false
p : loc
a : ℤ
b : 1 ≤ a
c : a < n + 1
⊢ { p ~~> ⟨↑(fact (a.toNat - 1))⟩ } [p := ⟨↑(fact (a.toNat - 1)) * a⟩] { x, p ~~> ⟨↑(fact a.toNat)⟩ }

9. `xsimp`: This tactic is used to simplify the heaps in the goal and often can be used to translate triples into pure goals after the program has been executed.

BEFORE STATE:

n : ℤ
h : 0 ≤ n
a✝ : decide (n = 0) = false
p : loc
⊢ (fun x ↦ p ~~> ⟨↑(fact (n + 1 - 1).toNat)⟩ ∗ emp) ===> fun x ↦ WP [!p] { hv, ⌜hv = ⟨↑(fact n.toNat)⟩⌝ ∗ ∃ʰ u, p ~~> u }

TACTIC APPLICATION: xsimp

AFTER STATE:

n : ℤ
h : 0 ≤ n
a✝ : decide (n = 0) = false
p : loc
r : val
⊢ p ~~> ⟨↑(fact (n + 1 - 1).toNat)⟩ ==> WP [!p] { hv, ⌜hv = ⟨↑(fact n.toNat)⟩⌝ ∗ ∃ʰ u, p ~~> u }

----------
""", 
"""
Now, provide your suggested tactic. Your output should consist of only the single Lean4 tactic. The tactic should be written as it would appear in a Lean4 proof, including any necessary arguments.

For example, your output might look like:
<tactic>xstep</tactic>

or

<tactic>xsimp</tactic>

or

<tactic>xfor (fun i => p ~~> (val_int (fact (i-1).toNat)))</tactic>

if the goal has no terms involving separation logic (that is, just math), for example:

n : ℤ
n_1✝ : True
⊢ n + n + (n + n) = 4 * n

then output:

<tactic>PURE</tactic>

If there are universal quantifiers or premises, you may need to use the `intro` tactic to introduce them before applying other tactics.

YOUR TASK: Given the following goal:

""" + goal + """

Find the correct tactic to use based on the term in the triple, or if no triple, say PURE. 
Remember, your final output should include only the single most appropriate Lean4 tactic enclosed in <tactic> tags, without any additional text or explanation.
Usually when xapp fails, you want to use xstep instead - PREFER `xstep` OVER xapp ALWAYS.
""")
