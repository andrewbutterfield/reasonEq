tryLawByName  :: Assertion -> String -> [ Int ] -> [ MatchContext ]
              -> YesBut ( Binding -- mapping from pattern to candidate
                        , Term -- autoInstantiated Law
                        , SideCond -- updated candidate side - condition
                        , SideCond ) -- discharged (?) law side - condition

tryLawByName asn@(Assertion tC scC) lnm parts mcs
  = do  ((( _ , asnP ) , _ ) , vts ) <- findLaw lnm mcs
        let tP = assnT asnP
        ( partsP , replP ) <- findParts parts tP
        let scP = assnC asnP
        bind <- match vts tC partsP       
        kbind <- bindKnown vts bind tP 
        fbind <- bindFloating vts kbind tP 
        tP' <- instantiate insctxt fbind replP
        scP' <- instantiateSC insctxt fbind scP
        scP'' <- scDischarge ( getDynamicObservables vts ) scC scP'
        return (fbind , tP' , scP' , scP'')
