module Keep
where

keep :: [(Bool, t -> Bool)] -> t -> Bool
keep [] mtch = True
keep s@((showit,isunusual):specs) mtch
  |  isunusual mtch && not showit  =  False
  |  otherwise = keep specs  mtch

