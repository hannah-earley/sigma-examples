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

; ---------------------------------- ;
; mu operators

; composition operators o_m^k
;  compose an m-ary h with m* k-ary g's
; again, we define a representative example
; observer that we don't need to specify k
;  by using a tuple for the input
(def O_2 {o_2 {(* F G1 G2 *)} o'_2})
(perm (o_2 {F {g1 g1z g1'} {g2 g2z g2'}} `o'_2 xs #)
      (`o1_2 F (g1 g1z g1' xs #) (g2 g2z g2' xs #) o_2))
(perm (o1_2 {f fz f'} (# y1 h1 g1 g1z g1') (# y2 h2 g2 g2z g2') `o_2)
      (`o'_2 (f fz f' {y1 y2} #) {{g1 g1z g1'} {g2 g2z g2'}} {h1 h2} o1_2))
(perm (o'_2 (# y h f fz f') {G1 G2} hs `o1_2)
      (# y {h hs} `o_2 {{f fz f'} G1 G2} o'_2))

; primitive recursion operators r_k
;  recurse using a k-ary zero case F
;   and a (k+2)-ary succ case G
;  resulting in a (k+1)-ary function
; we can't define this in one using tuples because
;  we need to modify the values in the (k+2)-tuples
; we could redefine this using lists to achieve that though
(def R_3 {r_3 {(* F G *)} r'_3})
(perm (r_3 {F G} `r_3' {{~n n'} x1 x2 x3} #)
      (~n [`rz_3 `rs_3] {F G n' {x1 x2 x3}} r_3))
  (perm (rz_3 [`r_3 `rs_3] {{f fz f'} G # xs} `zero)
        (`rz1_3 (f fz f' xs #) G rz_3))
    (perm (rz1_3 (# y h f fz f') G `rz_3)
          (`zero [`r'_3 `rs2_3] {y h {f fz f'} G} rz1_3))
  (perm (rs_3 [`rz_3 `r_3] {F G n {x1 x2 x3}} `succ)
        (`rs1_3 {n x1 x2 x3} (`r_3 {F G} `r'_3 {n x1 x2 x3} #) rs_3))
    (perm (rs1_3 {n x1 x2 x3} (# y h `r_3 {F {g gz g'}} `r'_3) `rs_3)
          (`rs2_3 F h (g gz g' {n y x1 x2 x3} #) rs1_3))
    (perm (rs2_3 F h (# y h' g gz g') `rs1_3)
          (`succ [`rz1_3 `r'_3] {y {h h'} F {g gz g'}} rs2_3))
(perm (r'_3 [`rz1_3 `rs2_3] {y h F G} ~h)
      (# y {~h h} `r_3 {F G} r'_3))

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
