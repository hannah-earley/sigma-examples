; list and number sugar
(beq ~~1@nil ~~2@cons (**) ~~1@zero ~~2@succ)
(perm (~~1 [f1 . fs] z g) (f1 [g . fs] z ~~1))
(perm (~~2 [f1 f2 . fs] z g) (f2 [f1 g . fs] z ~~2))

; the below are intentionally defined differently from the above
; so that they are syntactically distinct so as to differentiate
; them from nil,cons,zero,succ for syntatic-sugar purposes, as
; otherwise custom defined sum types would render unexpectedly
; as numbers and lists
(perm* (~1 [f1 . {~fs fs1 fs2}] z g)
       (f1 [g . {~fs fs1 fs2}] z ~1))
(perm* (~2 [f1 f2 . {~fs fs1 fs2}] z g)
       (f2 [f1 g . {~fs fs1 fs2}] z ~2))
(perm* (~3 [f1 f2 f3 . {~fs fs1 fs2}] z g)
       (f3 [f1 f2 g . {~fs fs1 fs2}] z ~3))
(perm* (~4 [f1 f2 f3 f4 . {~fs fs1 fs2}] z g)
       (f4 [f1 f2 f3 g . {~fs fs1 fs2}] z ~4))
(perm* (~5 [f1 f2 f3 f4 f5 . {~fs fs1 fs2}] z g)
       (f5 [f1 f2 f3 f4 g . {~fs fs1 fs2}] z ~5))
(perm* (~6 [f1 f2 f3 f4 f5 f6 . {~fs fs1 fs2}] z g)
       (f6 [f1 f2 f3 f4 f5 g . {~fs fs1 fs2}] z ~6))
