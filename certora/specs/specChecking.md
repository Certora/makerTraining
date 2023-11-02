

#  Checking spec:

1. If a rule is verified, are we done? no!
    - spec needs to be checks
    - spec can also have bugs
2. What is the coverage of the given spec ?
    - what is coverage ?
3. How can I check my spec ?
    - bug injection
    - review
    - sanity checks  
    - prover information

## Types of problem in rules
---
###  vacuity 

- a rule is violated when there is a state that reaches the assert and violates the assertion
- if there is no such state the rule can not be violated and therefore it is verified 

###  tautology 
- a rule that is verified regardless of the code

### low coverage
- a rule that is verified but only on a small subset of states\paths 

[run without any checks](https://prover.certora.com/output/40726/ae573916bde243929b216ccd73d891bf/?anonymousKey=f07d11423064e5267d597d2b3893ad7235d54b9f)
     -- vacuity and tautology passe

### missing rule
- which rule is still needed


     
## spec checking techniques
---
### rule_sanity 
 - [docs](https://docs.certora.com/en/latest/docs/prover/checking/sanity.html)

 - [basic](https://prover.certora.com/output/40726/2888f9b5c8194913b3a6f4e767a36036/?anonymousKey=b3d6ec3084f9a52e5e5c1072776ccb13a5b2d1c4)
    - no false positives
    - 


    [advance](https://prover.certora.com/output/40726/dd1624f0bd8045ed8c3730636f05529d/?anonymousKey=57e6cae5e7cc8403d3ac47dca2241955acd7e1d0) 
    - has false positives (e.g., onlyDenyRelyCanChange )
    - finds more problems (e.g, anotherTutology  privilegeAdvance)

    'certoraRun certora/conf/jugPlusBasicSanity.conf --msg "rule sanity advanced" --rule_sanity advanced  ' 


### bug_injection
 - manual and red-team  
    [example](https://prover.certora.com/output/40726/4b50cbbd95a74b838e61fee1249a3bc2/?anonymousKey=b2050c9a2ddab45329c49d2dc7abc31fd5cc3ad0) 
  
    notice change to :
    ```  
        //mutate switch mod(n, 2) case 0 { z := b } default { z := x }
          switch mod(n, 2) case 0 { z := x } default { z := b }
    ```
 - gambit (automatic bug injection and spec checking)
    [docs](https://docs.certora.com/en/latest/docs/gambit/index.html)

     `certoraMutate --prover_conf certora/conf/jugPlusBasicSanity.conf --mutation_conf certora/conf/mutateJug.conf`

     [results](https://mutation-testing.certora.com/?id=1e3efd41-d268-41e9-9a45-ab8f27a25ad6&anonymousKey=12462220-a74d-488c-864e-e2715c92194b)



### coverage information
 - unsat core

```
rule simple() {
    uint256 x;

    require x == someCompleCode(...);
    assert x >= 0;
}
```
```
rule multipleUC() { 
	bool a;
	bool b;	


	require a;
	require b;
	require !a;
	require !a || !b;


	assert false;	
}
```

```
     certoraRun certora/conf/jugPlusBasicSanity.conf --msg "coverage" --rule_sanity none --coverage_info advanced    
```

 - [results](https://prover.certora.com/output/40726/87999894fb3145e79808feea6a242307/UnsatCoreVisualisation.html?anonymousKey=1adcc07749ebf4c99624feb79a63141656d10406)     

## checking for unreachable issue
---
 - write the minimal rule
 - with coverage information
 [sanity rule](https://prover.certora.com/output/40726/7e8b84b8c4114e8f8e466a99350975a8/UnsatCoreVisualisation.html?anonymousKey=9340d433406d76eae452faed44ddca2528de7301)

- removing spec/code sections