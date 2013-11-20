/* Evaluations
 * Author: 
 * Creation date: mer. nov. 20 2013
 */
MACHINE
    Evaluations
SETS
    ETUDIANTS
    ; MODULES
    ; GROUPES
    ; PROJETS
   
VARIABLES
    lesEtudiants
    , lesModules
    , lesGroupes
    , lesProjets
    
INVARIANT
    lesEtudiants <: ETUDIANTS
    & lesModules <: MODULES
    & lesGroupes <: GROUPES
    & lesProjets <: PROJETS
    
    & moduleDe : PROJETS --> MODULES
    & groupeDe : ETUDIANTS <-> GROUPES
    
    
INITIALISATION
    lesEtudiants := ETUDIANTS
    || lesModules := MODULES
    || lesGroupes := GROUPES
    || lesProjets := PROJETS
    
 /*   || ann :: PERSONNES <-> NUMEROS*/
OPERATIONS
    donnerNumPersonne(num, pp) =
    PRE
        num : NUMEROS
        & pp : PERSONNES
        & (num <-> pp) /: ann
    THEN
        ann := ann \/ (num <-> pp)
    END
    ;
END
