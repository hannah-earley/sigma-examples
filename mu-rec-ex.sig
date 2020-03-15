(* mu recursive function proof of Turing completeness

 *  here we define functions as triples of F := (f z f')
     where f is the initiator perm, f' the final perm, and z any bound data

 *  we run a function F on an argument x as (f z f' x #) -> (# y h f z f')
     where h is any history data generated and y is the output

    n.b. we could do with only calling (f z x #) -> (# y z f')
         but then: 1. the history is part of the output
                   2. the caller must retain both f and f' to
                       reconstruct F and to remain reversible

 *  for higher arity functions we have a choice, we could either
     supply a tuple {x1 x2 ... xn}, or we could just splice in all n args
    here, we'll chose to use tuples *)

; define natural numbers
(inh "nat" zero succ)

; define lists
(inh "list" nil cons)

; ---------------------------------- ;
; mu functions

; constant function -- zero
(def Z {z # z})
(perm (z # `z x #) (# 0 x `z # z))

; successor function
(def S {s # s})
(perm (s # `s {n} #) (# {`succ n} # `s # s))

; projection functions p_i^k
;  there is an infinite family of these
;  here we define one as an example
(def P_2^4 {p_2^4 # p_2^4})
(perm (p_2^4 # `p_2^4 {x1 x2 x3 x4} #)
      (# x2 {x1 x3 x4} `p_2^4 # p_2^4))

(def P_1^1 {p_1^1 # p_1^1})
(perm (p_1^1 # `p_1^1 {x1} #)
      (# x1 {} `p_1^1 # p_1^1))

(def P_2^3 {p_2^3 # p_2^3})
(perm (p_2^3 # `p_2^3 {x1 x2 x3} #)
      (# x2 {x1 x3} `p_2^3 # p_2^3))

; ---------------------------------- ;
; mu operators

; composition operators o_m^k
;  compose an m-ary h with m* k-ary g's
; again, we define a representative example
; observer that we don't need to specify k
;  by using a tuple for the input
(def O_1 {o_1 {(* F G1 G2 *)} o'_1})
(perm (o_1 {F {g1 g1z g1'}} `o'_1 xs #)
      (`o1_1 F (g1 g1z g1' xs #) o_1))
(perm (o1_1 {f fz f'} (# y1 h1 g1 g1z g1') `o_1)
      (`o'_1 (f fz f' {y1} #) {g1 g1z g1'} h1 o1_1))
(perm (o'_1 (# y h f fz f') G1 hs `o1_1)
      (# y {h hs} `o_1 {{f fz f'} G1} o'_1))

; primitive recursion operators r_k
;  recurse using a k-ary zero case F
;   and a (k+2)-ary succ case G
;  resulting in a (k+1)-ary function
; we can't define this in one using tuples because
;  we need to modify the values in the (k+2)-tuples
; we could redefine this using lists to achieve that though
(def R_1 {r_1 {(* F G *)} r'_1})
(perm (r_1 {F G} `r'_1 {{~n n'} x1} #)
      (~n [`rz_1 `rs_1] {F G n' {x1}} r_1))
  (perm (rz_1 [`r_1 `rs_1] {{f fz f'} G # xs} `zero)
        (`rz1_1 (f fz f' xs #) G rz_1))
    (perm (rz1_1 (# y h f fz f') G `rz_1)
          (`zero [`r'_1 `rs2_1] {y h {f fz f'} G} rz1_1))
  (perm (rs_1 [`rz_1 `r_1] {F G n {x1}} `succ)
        (`rs1_1 {n x1} (`r_1 {F G} `r'_1 {n x1} #) rs_1))
    (perm (rs1_1 {n x1} (# y h `r_1 {F {g gz g'}} `r'_1) `rs_1)
          (`rs2_1 F h (g gz g' {n y x1} #) rs1_1))
    (perm (rs2_1 F h (# y h' g gz g') `rs1_1)
          (`succ [`rz1_1 `r'_1] {y {h h'} F {g gz g'}} rs2_1))
(perm (r'_1 [`rz1_1 `rs2_1] {y h F G} ~h)
      (# y {~h h} `r_1 {F G} r'_1))

; minimisation operator m_k
;  take a (k+1)-ary function F,
;  return a k-ary function
; minimisation finds the first zero of G(n)
;  where n is an integer and G(n) = F(n;xs)
(def M_3 (m_3 #(* F *) m'_3))
(perm (m_3 F `m'_3 xs #)
      (`zero [`ml_3 `mn_3] {F xs # #} m_3))
  (perm (ml_3 [`m_3 `mn_3] {{f fz f'} {x1 x2 x3} n' h} ~n)
        (`ms_3 {~n n'} {x1 x2 x3} h (f fz f' {{~n n'} x1 x2 x3} #) ml_3))
  (perm (ms_3 n xs h (# {~m m'} h' f fz f') `ml_3)
        (~m [`m'_3 `mn_3] {{f fz f'} xs n {h h' m'}} ms_3))
  (perm (mn_3 [`m'_3 `ms_3] a `succ)
        (`succ [`m_3 `ml_3] a mn_3))
(perm (m'_3 [`ms_3 `mn_3] {F xs n h} `zero)
      (# n {h xs} `m_3 F m'_3))

; ---------------------------------- ;

(perm (apply {f fz f'} xs #) (`apply' (f fz f' xs #) apply))
(perm (apply' (# y h f fz f') `apply) (# y h {f fz f'} apply'))

(perm (apply! {f fz f'} xs #) (`apply!' (f fz f' xs #) apply!))
(perm (apply!' (# y h f fz f') `apply!) (# y apply!'))

; ---------------------------------- ;
; example addition function
(beq*)
(def add {r_1 {P_1^1 {o_1 {S P_2^3} o'_1}} r'_1})
(def ex-add (r_1 {P_1^1 {o_1 {S P_2^3} o'_1}} r'_1 {23 47} #))
