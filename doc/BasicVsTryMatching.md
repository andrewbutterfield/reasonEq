# Basic vs Try Matching

## Basic Matching

```
basicMatch :: MatchClass
            -> [VarTable] -- known variables in scope at this law
            -> Law        -- law of interest
            -> Term       -- sub-part of law not being matched
            -> TermSC  -- candidate assertion
            -> Term       -- sub-part of law being matched
            -> Matches
basicMatch mc vts law@((n,asn@(Assertion tP scP)),_) repl asnC@(tC,scC) partsP
  =  do bind <- match vts tC partsP
        kbind <- bindKnown vts bind repl
        fbind <- bindFloating vts kbind repl
        let ictxt = mkInsCtxt scC
        scPinC <- instantiateSC ictxt fbind scP
        scD <- scDischarge ss scC scPinC

        if all isFloatingASC (fst scD)
          then do mrepl <- instantiate ictxt fbind repl
                  return $ MT n (unwrapASN asn) (chkPatn mc partsP)
                              fbind repl scC scPinC mrepl
          else fail "undischargeable s.c."

    chkPatn MatchEqvLHS (Var _ v)
      | lookupVarTables vts v == UnknownVar  =  MatchEqvVar 1
    chkPatn MatchEqvRHS (Var _ v)
      | lookupVarTables vts v == UnknownVar  =  MatchEqvVar 2
    chkPatn (MatchEqv [i]) (Var _ v)
      | lookupVarTables vts v == UnknownVar  =  MatchEqvVar i
    chkPatn mc _                             =  mc
```

```
ss = S.elems $ S.map theSubscript $ S.filter isDuring
             $ S.map gvarWhen $ mentionedVars tC
```


## Try Matching

### Actual

```
tryLawByName asn@(Assertion tC scC) lnm parts mcs
  = do (((_,asnP),_),vts) <- findLaw lnm mcs
       let tP = assnT asnP 
       (partsP,replP) <- findParts parts tP
       bind <- match vts tC partsP
       let scP = assnC asnP
       kbind <- bindKnown vts bind tP
       fbind <- bindFloating vts kbind tP
       let insctxt = mkInsCtxt scC
       tP' <-  instantiate insctxt fbind replP -- 
       scP' <- instantiateSC insctxt fbind scP
       scP'' <- scDischarge ss scC scP'
       -- basic: if all isFloatingASC (fst scP'') ...
       return (fbind,tP',scP',scP'')
 
\end{code}
```


### Idea

```
tryLawByName :: Assertion -> String -> [Int] -> [MatchContext]
               -> YesBut ( Binding    -- mapping from pattern to candidate
                         , Term       -- autoInstantiated Law
                         , SideCond   -- updated candidate side-condition
                         , SideCond ) -- discharged(?) law side-condition
tryLawByName asn@(Assertion tC scC) lnm parts mcs
  = do (((_,asnP),_),vts) <- findLaw lnm mcs
       let tP = assnT asnP
       partsP <- findParts parts tP
       tryMatch vts tP partsP $ assnC asnP
    -- bind          <- match vts tC partsP
    -- (kbind,tPasC) <- bindKnown vts bind tP
    -- (fbind,_)     <- bindFloating vts kbind tP
    -- tP'           <- instantiate fbind tP
    -- scP'          <- instantiateSC fbind scP 
    -- scP''         <- scDischarge scC scP' of
    -- return (fbind,tP',scP',scP'')
```

