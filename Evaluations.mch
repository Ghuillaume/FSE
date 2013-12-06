/* Evaluations
 * Author: 
 * Creation date: mer. nov. 20 2013
 */
MACHINE
    Evaluations
SETS
    ETUDIANT
    ; MODULE
    ; GROUPE
    ; PROJET
   
VARIABLES
    /* Sets */
    etudiants
    , modules
    , groupes
    , projets
    
    /* Relations */
    , est_inscrit_a
    , module_de
    , realise_par
    , realise_par_groupe
    , note
    
INVARIANT
    etudiants <: ETUDIANT
    & modules <: MODULE
    & groupes <: GROUPE
    & projets <: PROJET
    
    & est_inscrit_a : etudiants <-> modules
    & module_de : projets --> modules
    & realise_par : projets <-> etudiants
    & realise_par_groupe : projets +-> groupes
    
    & note : (etudiants * modules) +-> NAT
            
    & !ee.( (ee : ETUDIANT) =>
                ( ( (realise_par~[{ee}] <| module_de |> est_inscrit_a[{ee}]) ) : (realise_par~[{ee}] >+> est_inscrit_a[{ee}])) ) 
    
    
    
    /* ESSAIS ANTÉRIEURS */
    
    /*& !mm.( mm : MODULE => 
        ( !ee.( (ee : ETUDIANT) =>
                	( card( realise_par~[{ee}] /\ module_de~[{mm}] ) <= 1 ) )
         ))*/
    
    /*& !ee.( (ee : ETUDIANT) =>
                ( ( (realise_par~[{ee}] --> est_inscrit_a[{ee}]) ) <: (realise_par~[{ee}] >+> modules) ) )
            */
                
    /*& !ee.( (ee : ETUDIANT) =>
                ( ( {ee} <| module_de) : (realise_par~[{ee}] >+> est_inscrit_a[{ee}])) )*/
         
     

INITIALISATION
    etudiants := {}
    || modules := {}
    || groupes := {}
    || projets := {}
    
    || est_inscrit_a := {}
    || module_de := {}
    || realise_par := {}
    || realise_par_groupe := {}
    || note := {}
    
OPERATIONS
    
    /*
     * QUESTION 1.A
     */
    inscrire_etudiant_module(ee, mm) =
    PRE
        ee : ETUDIANT
        & ee : etudiants
        & mm : MODULE
        & mm : modules
        
        /* L'étudiant n'est pas déjà inscrit à mm */
        & ee |-> mm /: est_inscrit_a
        
        /* l'étudiant n'est pas affecté à un projet de mm */
        & mm |-> ee /: (module_de~ ; realise_par)
        
    THEN
        est_inscrit_a := est_inscrit_a \/ {ee |-> mm}
    END
    ;
    
    /* PO4 (invariant est_dans_groupe <: ( realise_par~ ; realise_par_groupe ))
    --> prouvée en IP */
    desinscrire_etudiant_module(ee, mm) =
    PRE
        ee : ETUDIANT
        & ee : etudiants
        & mm : MODULE
        & mm : modules
        
        /* L'étudiant est inscrit à mm */
        & ee |-> mm : est_inscrit_a
        
    THEN
        /* Desinscrire l'étudiant + le désafecter des projets */
        est_inscrit_a := est_inscrit_a - {ee |-> mm}
        || ANY projet WHERE projet : PROJET & projet = module_de~(mm) THEN
            realise_par := realise_par - { projet |-> ee }
        END
    END
    ;
    
    inscrire_etudiant_projet(ee, pp) =
    PRE
        ee : ETUDIANT
        & ee : etudiants
        & pp : PROJET
        & pp : projets
        
        /* l'étudiant ne travaille pas déjà sur un projet du même module que pp */
        & module_de(pp) /: module_de[realise_par~[{ee}]]
        
        /* l'étudiant est inscrit au module */
        & ee : est_inscrit_a~[module_de[{pp}]]
    THEN
        realise_par := realise_par \/ {pp |-> ee}
    END
    ;
    
    /* PO3 (invariant est_dans_groupe <: ( realise_par~ ; realise_par_groupe ))
    --> prouvée en IP */
    desinscrire_etudiant_projet(ee, pp) =
    PRE
        ee : ETUDIANT
        & ee : etudiants
        & pp : PROJET
        & pp : projets
        
        /* l'étudiant travaille sur pp */
        & pp |-> ee : realise_par
    THEN
        realise_par := realise_par - {pp |-> ee}
    END
    ;
    
    /*
     * QUESTION 1.B
     */
     
    ajouter_module(mm) =
    PRE
        mm : MODULE
        & mm /: modules
    THEN
        modules := modules \/ {mm}
    END
    ;
    
    ajouter_groupe(gg) =
    PRE
        gg : GROUPE
        & gg /: groupes
    THEN
        groupes := groupes \/ {gg}
    END
    ;
    
    /* Pourquoi on peut pas prouver ??
    On vérifie que mm et pp ne sont dans aucune relation
    L'invariant devrait être vérifié....*/
    ajouter_projet(pp, mm) =
    PRE
        pp : PROJET
        & pp /: projets
        & mm : MODULE
        & mm : modules
    THEN
        projets := projets \/ {pp}
        || module_de := module_de \/ {pp |-> mm}
    END
    ;
    
    affecter_groupe(gg, pp) =
    PRE
        gg : GROUPE
        & gg : groupes
        & pp : PROJET
        & pp : projets
        
        & pp /: dom(realise_par_groupe)
    THEN
        realise_par_groupe := realise_par_groupe \/ {pp |-> gg}
    END
    ;
    
    ajouter_etudiant(ee) =
    PRE
        ee : ETUDIANT
        & ee /: etudiants
    THEN
        etudiants := etudiants \/ {ee}
    END
    ;
   
    
    /*
     * QUESTION 1.C
     */
    gg <-- liste_groupes(ee) =
    PRE
        ee : ETUDIANT
        & ee : etudiants
    THEN
        gg := realise_par_groupe[realise_par~[{ee}]]
    END
    ;
    
    
    /*
     * QUESTION 1.D
     * return : Nombre de projets sur lequel travaille l'étudiant et ensemble de ces projets
     */
    nn,pp <-- liste_projets(ee) =
    PRE
        ee : ETUDIANT
        & ee : etudiants
    THEN
        pp := realise_par~[{ee}]
        || nn := card(realise_par~[{ee}])
    END
    ;
   
    
    /*
     * QUESTION 1.E
     */
    ee <-- participent_a_plus_de(nn) =
    PRE
        nn : NAT
        & ee <: ETUDIANT
    THEN
        ANY etudiant WHERE etudiant : ETUDIANT & etudiant : etudiants THEN
            IF (card(realise_par_groupe[realise_par~[ee]]) > nn)
            THEN ee := ee \/ {etudiant}
            END
        END

    END
    ;
    
    /*
    * QUESTIONS SUPPLÉMENTAIRES
    *
    */
    nn <-- obtenir_note(ee, mm) =
    PRE
        ee : ETUDIANT
        & ee : etudiants
        & mm : MODULE
        & mm : modules
        & (ee |-> mm) : dom(note)
        & (ee |-> mm) : est_inscrit_a
    THEN
        nn := note(ee, mm)
    END
    ;
    
    saisir_note(ee, mm, nn) =
    PRE
        ee : ETUDIANT
        & ee : etudiants
        & mm : MODULE
        & mm : modules
        & nn : NAT
        & (ee |-> mm) : est_inscrit_a
    THEN
        note(ee,mm) := nn
    END
    ;
    
    ee <-- etudiants_sans_note =
    PRE
        ee <: ETUDIANT
    THEN
        ANY etudiant WHERE etudiant : ETUDIANT & etudiant : etudiants THEN
            IF (etudiant /: dom(dom(note)))
            THEN ee := ee \/ {etudiant}
            END
        END
	END
    
END
