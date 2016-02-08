; atoms
(def {nil} {})
(def {true} 1)
(def {false} 0)
; function definition
(def {fun} (\ {f b} {
  def (head f) (\ (tail f) b)
}))
; unpack list for function
(fun {unpack f l} {
  eval (join (list f) l)
})
; pack list for function
(fun {pack f & xs} {f xs})
; curried and uncurried calling
(def {curry} unpack)
(def {uncurry} pack)
; perform several things in sequence
(fun {do & l} {
  if (== l nil)
    {nil}
    {last l}
})
; open new scope
(fun {let b} {
  ((\ {_} b) ())
})
; logical functions
(fun {not x} {- 1 x})
(fun {or x y} {+ x y})
(fun {and x y} {* x y})
; miscellaneous
(fun {flip fn a b} {fn b a}) ; uses fn with flipped args
(fun {ghost & xs} {eval xs}) ; useless function?
(fun {comp fn g x} {fn (g x)}) ; uses g with x and feed it to fn
; first, second or third list item
(fun {fst l} { eval (head l) })
(fun {snd l} { eval (head (tail l)) })
(fun {trd l} { eval (head (tail (tail l))) })
; list lenght
(fun {len l} {
  if (== l nil)
    {0}
    {+ 1 (len (tail l))}
})
; nth item in list
(fun {nth n l} {
  if (== n 0)
    {fst l}
    {nth (- n 1) (tail l)}
})
; last item in list
(fun {last l} {nth (- (len l) 1) l})
; take n items
(fun {take n l} {
  if (== n 0)
    {nil}
    {join (head l) (take (- n 1) (tail l))}
})
; drop n items
(fun {drop n l} {
  if (== n 0)
    {l}
    {drop (- n 1) (tail l)}
})
; split at n
(fun {split n l} {list (take n l) (drop n l)})
; element of list
(fun {elem x l} {
  if (== l nil)
    {false}
    {if (== x (fst l)) {true} {elem x (tail l)}}
})
; apply function to list
(fun {map f l} {
  if (== l nil)
    {nil}
    {join (list (f (fst l))) (map f (tail l))}
})
; apply filter to list
(fun {filter f l} {
  if (== l nil)
    {nil}
    {join (if (f (fst l)) {head l} {nil}) (filter f (tail l))}
})
; fold left
(fun {reduce f z l} {
  if (== l nil)
    {z}
    {reduce f (f z (fst l)) (tail l)}
})
; sum and product
(fun {sum l} {reduce + 0 l})
(fun {prod l} {reduce * 1 l})
; select & case & otherwise
(def {otherwise} true)
(fun {case x & cs} {
  if (== cs nil)
    {error "no case found"}
    {if (== x (fst (fst cs)))
      {snd (fst cs)}
      {unpack case (join (list x) (tail cs))}
    }
})
(fun {select & cs} {
  if (== cs nil)
    {error "selection not found"}
    {if (fst (fst cs)) {snd (fst cs)} {unpack select (tail cs)}}
})