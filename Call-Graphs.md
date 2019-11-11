# Call Graphs

## Matching

### LiveProofs


`tryLawByName`  calls `match` `completeBind` `instantiateSC` `scDischarged`

`matchInContexts` calls `matchLaws`

`matchLaws` calls `domatch`

`matchLawByName` calls `domatch`

`domatch` calls `basicMatch` `doPartialMatch`

`doPartialMatch` calls `doEqvMatch` `basicMatch`

`doEqvMatch` calls `doEqvMatchB` `doEqvMatchC`

`doEqvMatchB` calls `basicMatch`

`doEqvMatchC` calls `doEqvMatchC'`

`doEqvMatchC'` calls `basicMatch`

`basicMatch` calls `match` `completeBind` `instantiateSC` `scDischarged` `instantiate`

# That's all folks!
