same_cons : {xs : List a} -> {ys : List a} ->
            xs = ys -> x :: xs = x :: ys
same_cons Refl = Refl

same_lists : {xs : List a} -> {ys : List a} ->
             x = y -> xs = ys -> x :: xs = y :: ys
same_lists prf1 prf2 =
                      rewrite sym prf1
                      in rewrite same_cons prf2
                      in ?hooole
