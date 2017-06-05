(* a function is defined as a triplet F = {f z f'}, where f is the initiator
   permutation, z is a local environment akin to a closure, and f' is the
   terminator permutation; the idea is that:
     (f z f' a #) <-> (# r f z f')
   these higher level structures are much more generally composable than
   regular permutations, as for example you can now create a function map
   that takes another function and applies it to a list; you could then also
   consider currying such that you can create a curried +, to which you
   associate a value, say 2, and then you can bind (+2) to map and then
   apply it to a list

   this file contains functions that operate on functions, and also functions/
   permutations that lift permutations -> functions; it is not possible to go
   the other way... *)

; lift perms of various arity to functions
;; perms taking n0 arguments, and returning 0, 1, or 2 results
(beq lift'0'0 lift'0'0' lift'0'1 lift'0'1' lift'0'2 lift'0'2')
(grp
  (perm* (lift'0'0 {p p'} `lift'0'0' {} #)
         (`lift'0'0' (p #) p p' lift'0'0))
  (perm* (lift'0'0' (# p') p p' `lift'0'0)
         (# {} `lift'0'0 {p p'} `lift'0'0')))
(grp
  (perm* (lift'0'1 {p p'} `lift'0'1' {} #)
         (`lift'0'1' (p #) p p' lift'0'1))
  (perm* (lift'0'1' (# r p') p p' `lift'0'1)
         (# {r} `lift'0'1 {p p'} `lift'0'1')))
(grp
  (perm* (lift'0'2 {p p'} `lift'0'2' {} #)
         (`lift'0'2' (p #) p p' lift'0'2))
  (perm* (lift'0'2' (# r1 r2 p') p p' `lift'0'2)
         (# {r1 r2} `lift'0'2 {p p'} `lift'0'2')))
;; perms taking 1 argument, and returning 0, 1, or 2 results
(beq lift'1'0 lift'1'0' lift'1'1 lift'1'1' lift'1'2 lift'1'2')
(grp
  (perm* (lift'1'0 {p p'} `lift'1'0' {a} #)
         (`lift'1'0' (p a #) p p' lift'1'0))
  (perm* (lift'1'0' (# p') p p' `lift'1'0)
         (# {} `lift'1'0 {p p'} `lift'1'0')))
(grp
  (perm* (lift'1'1 {p p'} `lift'1'1' {a} #)
         (`lift'1'1' (p a #) p p' lift'1'1))
  (perm* (lift'1'1' (# r p') p p' `lift'1'1)
         (# {r} `lift'1'1 {p p'} `lift'1'1')))
(grp
  (perm* (lift'1'2 {p p'} `lift'1'2' {a} #)
         (`lift'1'2' (p a #) p p' lift'1'2))
  (perm* (lift'1'2' (# r1 r2 p') p p' `lift'1'2)
         (# {r1 r2} `lift'1'2 {p p'} `lift'1'2')))
;; perms taking 2 arguments, and returning 0, 1, or 2 results
(beq lift'2'0 lift'2'0' lift'2'1 lift'2'1' lift'2'2 lift'2'2')
(grp
  (perm* (lift'2'0 {p p'} `lift'2'0' {a b} #)
         (`lift'2'0' (p a b #) p p' lift'2'0))
  (perm* (lift'2'0' (# p') p p' `lift'2'0)
         (# {} `lift'2'0 {p p'} `lift'2'0')))
(grp
  (perm* (lift'2'1 {p p'} `lift'2'1' {a b} #)
         (`lift'2'1' (p a b #) p p' lift'2'1))
  (perm* (lift'2'1' (# r p') p p' `lift'2'1)
         (# {r} `lift'2'1 {p p'} `lift'2'1')))
(grp
  (perm* (lift'2'2 {p p'} `lift'2'2' {a b} #)
         (`lift'2'2' (p a b #) p p' lift'2'2))
  (perm* (lift'2'2' (# r1 r2 p') p p' `lift'2'2)
         (# {r1 r2} `lift'2'2 {p p'} `lift'2'2')))

; lift choice perm over perms to choice function over functions;
; note that because we can only instantiate a subseq from top/bottom,
; we first swap F_n with # (due to the way ~n works), then we
; extract F_n, replace it with G, and run ~n backwards to complete
; the swap of F_n with G inside Fs
(beq ~ ~')
(grp
  (perm* (~ ~n `~' {Fs G} #) (`~'1 (~n Fs # #) G ~))
   ; need to assert F == {f fz f'} and G == {g gz g'}
   ; so that the subseq can be proven terminating
  (perm  (~'1 ({f fz f'} Fs' # ~n) {g gz g'} `~)
         (`~' {f fz f'} ({g gz g'} Fs' # ~n) ~'1))
  (perm* (~' F (~n Fs'' # #) `~'1) (# {F Fs''} `~ ~n ~')))

; run F backwards
(beq back back')
(grp
  (perm* (back {f fz f'} `back' a #) (`back' (# a f fz f') back))
  (perm* (back' (f fz f' r #) `back) (# r `back {f fz f'} back')))

; compose F . G
(beq comp comp')
(grp
  (perm* (comp {{f fz f'} G} `comp' a #) (`comp'1 G (f fz f' a #) comp))
  (perm (comp'1 {g gz g'} (# b f fz f') `comp)
        (`comp' {f fz f'} (g gz g' b #) comp'1))
  (perm* (comp' F (# r g gz g') `comp'1) (# r `comp {F {g gz g'}} comp')))
