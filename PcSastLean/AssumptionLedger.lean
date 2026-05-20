import PcSastLean.SourceBackedNoOrphanCPG

/-!
Assumption ledger.

This file keeps the top-level claim boundary explicit.  Most modules in this
repository prove conditional soundness theorems for a deliberately small IR or
for certificate languages.  Source-level SAST claims require external
obligations, especially extraction soundness, analyzer soundness, and complete
proof-carrying triage.
-/

namespace PcSastLean

inductive ModeledSurface where
  | toyExprTaint
  | linearSecurityIR
  | miniSourceLanguage
  | miniSourceBranches
  | miniSourceExceptions
  | miniSourceCallbacks
  | richSourceProvenance
  | sourceBackedNoOrphanCPG
  | branchJoin
  | procedureSummaries
  | heapMayAlias
  | pointerArithmetic
  | sanitizerCapabilities
  | propositionalResolution
  | routeTemplates
  | routeShadowSuppression
  | pointerDisjointSuppression
  | ifdsCertificates
  | ifdsDistributiveFlows
  | cpgCertificates
  | cpgComponentMerge
  | cpgExtractionProvenance
  | cpgTraversalTemplates
  | cpgNodePredicates
  | cpgPolicyProvenance
  | cpgSanitizerPolicy
  | cpgOrderedSanitizer
  | cpgSanitizerTriage
  | cpgSanitizerGuardrail
  | cpgNoOrphanAdapter
  | ciTriage
deriving DecidableEq, Repr

inductive ExternalObligation where
  | realLanguageExtraction
  | dynamicSummarySoundness
  | frameworkExtractionSoundness
  | richSMTTheoryProofs
  | cpgExtractionProvenance
  | precisionEvaluation
deriving DecidableEq, Repr

inductive ClaimStatus where
  | verified
  | conditional
  | externalObligation
  | notModeled
deriving DecidableEq, Repr

inductive ModuleName where
  | basic
  | securityIR
  | heapIR
  | extractionGate
  | miniSourceExtraction
  | miniSourceBranch
  | miniSourceException
  | miniSourceCallback
  | richSourceProvenance
  | sourceBackedNoOrphanCPG
  | ifds
  | ifdsDistributive
  | ifdsSummary
  | cpg
  | cpgConstruction
  | cpgExtractionProvenance
  | cpgTraversal
  | cpgNodePredicates
  | cpgPolicyProvenance
  | cpgSanitizerPolicy
  | cpgOrderedSanitizer
  | cpgSanitizerTriage
  | cpgSanitizerGuardrail
  | cpgNoOrphanAdapter
  | cpgProvenance
  | smtCore
  | smtResolution
  | framework
  | frameworkTemplate
  | frameworkShadowSuppression
  | objectSensitive
  | pointerArithmetic
  | pointerDisjointSuppression
  | ciGate
deriving DecidableEq, Repr

structure ModuleClaim where
  module : ModuleName
  status : ClaimStatus
  modeled : List ModeledSurface
  obligations : List ExternalObligation
deriving Repr

structure SourceLevelGateInputs where
  sourceViolations : List Node
  run : AnalyzerRun
  triage : TriageRun
  extraction : SourceToIRSound sourceViolations run.concrete
  analyzerSound : run.Sound
  triageComplete : triage.Complete run

theorem source_level_ci_no_bug_hiding
    (inputs : SourceLevelGateInputs) :
    ListSubset inputs.sourceViolations inputs.triage.report := by
  exact ListSubset.trans
    inputs.extraction
    (ci_gate_no_bug_hiding inputs.analyzerSound inputs.triageComplete)

structure VerifiedSliceBoundary where
  modeled : List ModeledSurface
  obligations : List ExternalObligation

def currentSliceBoundary : VerifiedSliceBoundary :=
  { modeled :=
      [ ModeledSurface.toyExprTaint
      , ModeledSurface.linearSecurityIR
      , ModeledSurface.miniSourceLanguage
      , ModeledSurface.branchJoin
      , ModeledSurface.procedureSummaries
      , ModeledSurface.heapMayAlias
      , ModeledSurface.pointerArithmetic
      , ModeledSurface.pointerDisjointSuppression
      , ModeledSurface.sanitizerCapabilities
      , ModeledSurface.sourceBackedNoOrphanCPG
      , ModeledSurface.ifdsCertificates
      , ModeledSurface.ifdsDistributiveFlows
      , ModeledSurface.cpgCertificates
      , ModeledSurface.cpgComponentMerge
      , ModeledSurface.cpgExtractionProvenance
      , ModeledSurface.cpgTraversalTemplates
      , ModeledSurface.cpgNodePredicates
      , ModeledSurface.cpgPolicyProvenance
      , ModeledSurface.cpgSanitizerPolicy
      , ModeledSurface.cpgOrderedSanitizer
      , ModeledSurface.cpgSanitizerTriage
      , ModeledSurface.cpgSanitizerGuardrail
      , ModeledSurface.cpgNoOrphanAdapter
      , ModeledSurface.ciTriage
      ]
  , obligations :=
      [ ExternalObligation.realLanguageExtraction
      , ExternalObligation.dynamicSummarySoundness
      , ExternalObligation.frameworkExtractionSoundness
      , ExternalObligation.richSMTTheoryProofs
      , ExternalObligation.cpgExtractionProvenance
      , ExternalObligation.precisionEvaluation
      ]
  }

example : ExternalObligation.realLanguageExtraction ∈ currentSliceBoundary.obligations := by
  simp [currentSliceBoundary]

def moduleClaimLedger : List ModuleClaim :=
  [ { module := ModuleName.basic
    , status := ClaimStatus.verified
    , modeled := [ModeledSurface.toyExprTaint]
    , obligations := []
    }
  , { module := ModuleName.securityIR
    , status := ClaimStatus.conditional
    , modeled :=
        [ModeledSurface.linearSecurityIR, ModeledSurface.branchJoin,
          ModeledSurface.procedureSummaries]
    , obligations := [ExternalObligation.dynamicSummarySoundness]
    }
  , { module := ModuleName.heapIR
    , status := ClaimStatus.conditional
    , modeled := [ModeledSurface.heapMayAlias]
    , obligations := []
    }
  , { module := ModuleName.extractionGate
    , status := ClaimStatus.externalObligation
    , modeled := []
    , obligations := [ExternalObligation.realLanguageExtraction]
    }
  , { module := ModuleName.miniSourceExtraction
    , status := ClaimStatus.verified
    , modeled := [ModeledSurface.miniSourceLanguage]
    , obligations := []
    }
  , { module := ModuleName.miniSourceBranch
    , status := ClaimStatus.verified
    , modeled := [ModeledSurface.miniSourceLanguage, ModeledSurface.miniSourceBranches]
    , obligations := []
    }
  , { module := ModuleName.miniSourceException
    , status := ClaimStatus.verified
    , modeled :=
        [ModeledSurface.miniSourceLanguage, ModeledSurface.miniSourceExceptions]
    , obligations := []
    }
  , { module := ModuleName.miniSourceCallback
    , status := ClaimStatus.verified
    , modeled :=
        [ModeledSurface.miniSourceLanguage, ModeledSurface.miniSourceCallbacks]
    , obligations := []
    }
  , { module := ModuleName.richSourceProvenance
    , status := ClaimStatus.conditional
    , modeled := [ModeledSurface.richSourceProvenance]
    , obligations := [ExternalObligation.realLanguageExtraction]
    }
  , { module := ModuleName.sourceBackedNoOrphanCPG
    , status := ClaimStatus.conditional
    , modeled :=
        [ModeledSurface.richSourceProvenance,
          ModeledSurface.sourceBackedNoOrphanCPG,
          ModeledSurface.cpgCertificates, ModeledSurface.cpgComponentMerge,
          ModeledSurface.cpgExtractionProvenance,
          ModeledSurface.cpgNoOrphanAdapter]
    , obligations :=
        [ExternalObligation.realLanguageExtraction,
          ExternalObligation.cpgExtractionProvenance]
    }
  , { module := ModuleName.ifds
    , status := ClaimStatus.verified
    , modeled := [ModeledSurface.ifdsCertificates]
    , obligations := []
    }
  , { module := ModuleName.ifdsDistributive
    , status := ClaimStatus.conditional
    , modeled := [ModeledSurface.ifdsCertificates, ModeledSurface.ifdsDistributiveFlows]
    , obligations := [ExternalObligation.realLanguageExtraction]
    }
  , { module := ModuleName.ifdsSummary
    , status := ClaimStatus.verified
    , modeled := [ModeledSurface.ifdsCertificates]
    , obligations := []
    }
  , { module := ModuleName.cpg
    , status := ClaimStatus.conditional
    , modeled := [ModeledSurface.cpgCertificates]
    , obligations := [ExternalObligation.cpgExtractionProvenance]
    }
  , { module := ModuleName.cpgConstruction
    , status := ClaimStatus.conditional
    , modeled := [ModeledSurface.cpgCertificates, ModeledSurface.cpgComponentMerge]
    , obligations := [ExternalObligation.cpgExtractionProvenance]
    }
  , { module := ModuleName.cpgExtractionProvenance
    , status := ClaimStatus.conditional
    , modeled :=
        [ModeledSurface.cpgCertificates, ModeledSurface.cpgComponentMerge,
          ModeledSurface.cpgExtractionProvenance]
    , obligations := [ExternalObligation.cpgExtractionProvenance]
    }
  , { module := ModuleName.cpgTraversal
    , status := ClaimStatus.conditional
    , modeled := [ModeledSurface.cpgCertificates, ModeledSurface.cpgTraversalTemplates]
    , obligations := [ExternalObligation.cpgExtractionProvenance]
    }
  , { module := ModuleName.cpgNodePredicates
    , status := ClaimStatus.conditional
    , modeled :=
        [ModeledSurface.cpgCertificates, ModeledSurface.cpgTraversalTemplates,
          ModeledSurface.cpgNodePredicates]
    , obligations := [ExternalObligation.cpgExtractionProvenance]
    }
  , { module := ModuleName.cpgPolicyProvenance
    , status := ClaimStatus.conditional
    , modeled :=
        [ModeledSurface.cpgCertificates, ModeledSurface.cpgTraversalTemplates,
          ModeledSurface.cpgNodePredicates, ModeledSurface.cpgPolicyProvenance]
    , obligations := [ExternalObligation.cpgExtractionProvenance]
    }
  , { module := ModuleName.cpgSanitizerPolicy
    , status := ClaimStatus.conditional
    , modeled :=
        [ModeledSurface.cpgCertificates, ModeledSurface.cpgTraversalTemplates,
          ModeledSurface.cpgNodePredicates, ModeledSurface.cpgPolicyProvenance,
          ModeledSurface.cpgSanitizerPolicy, ModeledSurface.sanitizerCapabilities]
    , obligations := [ExternalObligation.cpgExtractionProvenance]
    }
  , { module := ModuleName.cpgOrderedSanitizer
    , status := ClaimStatus.conditional
    , modeled :=
        [ModeledSurface.cpgCertificates, ModeledSurface.cpgTraversalTemplates,
          ModeledSurface.cpgNodePredicates, ModeledSurface.cpgPolicyProvenance,
          ModeledSurface.cpgSanitizerPolicy, ModeledSurface.cpgOrderedSanitizer,
          ModeledSurface.sanitizerCapabilities]
    , obligations := [ExternalObligation.cpgExtractionProvenance]
    }
  , { module := ModuleName.cpgSanitizerTriage
    , status := ClaimStatus.conditional
    , modeled :=
        [ModeledSurface.cpgCertificates, ModeledSurface.cpgTraversalTemplates,
          ModeledSurface.cpgNodePredicates, ModeledSurface.cpgPolicyProvenance,
          ModeledSurface.cpgSanitizerPolicy, ModeledSurface.cpgOrderedSanitizer,
          ModeledSurface.cpgSanitizerTriage, ModeledSurface.sanitizerCapabilities,
          ModeledSurface.ciTriage]
    , obligations :=
        [ExternalObligation.cpgExtractionProvenance,
          ExternalObligation.precisionEvaluation]
    }
  , { module := ModuleName.cpgSanitizerGuardrail
    , status := ClaimStatus.conditional
    , modeled :=
        [ModeledSurface.cpgCertificates, ModeledSurface.cpgTraversalTemplates,
          ModeledSurface.cpgNodePredicates, ModeledSurface.cpgPolicyProvenance,
          ModeledSurface.cpgSanitizerPolicy, ModeledSurface.cpgOrderedSanitizer,
          ModeledSurface.cpgSanitizerTriage,
          ModeledSurface.cpgSanitizerGuardrail,
          ModeledSurface.sanitizerCapabilities, ModeledSurface.ciTriage]
    , obligations :=
        [ExternalObligation.cpgExtractionProvenance,
          ExternalObligation.precisionEvaluation]
    }
  , { module := ModuleName.cpgNoOrphanAdapter
    , status := ClaimStatus.conditional
    , modeled :=
        [ModeledSurface.cpgCertificates, ModeledSurface.cpgComponentMerge,
          ModeledSurface.cpgExtractionProvenance,
          ModeledSurface.cpgTraversalTemplates,
          ModeledSurface.cpgNodePredicates, ModeledSurface.cpgPolicyProvenance,
          ModeledSurface.cpgSanitizerPolicy, ModeledSurface.cpgOrderedSanitizer,
          ModeledSurface.cpgSanitizerTriage,
          ModeledSurface.cpgNoOrphanAdapter,
          ModeledSurface.sanitizerCapabilities, ModeledSurface.ciTriage]
    , obligations :=
        [ExternalObligation.cpgExtractionProvenance,
          ExternalObligation.precisionEvaluation]
    }
  , { module := ModuleName.cpgProvenance
    , status := ClaimStatus.conditional
    , modeled := [ModeledSurface.cpgCertificates, ModeledSurface.cpgExtractionProvenance]
    , obligations := [ExternalObligation.cpgExtractionProvenance]
    }
  , { module := ModuleName.smtCore
    , status := ClaimStatus.conditional
    , modeled := []
    , obligations := [ExternalObligation.richSMTTheoryProofs]
    }
  , { module := ModuleName.smtResolution
    , status := ClaimStatus.conditional
    , modeled := [ModeledSurface.propositionalResolution]
    , obligations := [ExternalObligation.richSMTTheoryProofs]
    }
  , { module := ModuleName.framework
    , status := ClaimStatus.conditional
    , modeled := []
    , obligations := [ExternalObligation.frameworkExtractionSoundness]
    }
  , { module := ModuleName.frameworkTemplate
    , status := ClaimStatus.conditional
    , modeled := [ModeledSurface.routeTemplates]
    , obligations := [ExternalObligation.frameworkExtractionSoundness]
    }
  , { module := ModuleName.frameworkShadowSuppression
    , status := ClaimStatus.conditional
    , modeled := [ModeledSurface.routeTemplates, ModeledSurface.routeShadowSuppression]
    , obligations := [ExternalObligation.frameworkExtractionSoundness]
    }
  , { module := ModuleName.objectSensitive
    , status := ClaimStatus.conditional
    , modeled := [ModeledSurface.heapMayAlias]
    , obligations := []
    }
  , { module := ModuleName.pointerArithmetic
    , status := ClaimStatus.conditional
    , modeled := [ModeledSurface.heapMayAlias, ModeledSurface.pointerArithmetic]
    , obligations := [ExternalObligation.realLanguageExtraction]
    }
  , { module := ModuleName.pointerDisjointSuppression
    , status := ClaimStatus.conditional
    , modeled :=
        [ModeledSurface.heapMayAlias, ModeledSurface.pointerArithmetic,
          ModeledSurface.pointerDisjointSuppression]
    , obligations := [ExternalObligation.realLanguageExtraction]
    }
  , { module := ModuleName.ciGate
    , status := ClaimStatus.conditional
    , modeled := [ModeledSurface.ciTriage]
    , obligations :=
        [ExternalObligation.realLanguageExtraction,
          ExternalObligation.precisionEvaluation]
    }
  ]

def ModuleHasStatus (module : ModuleName) (status : ClaimStatus) : Prop :=
  exists claim, claim ∈ moduleClaimLedger /\ claim.module = module /\ claim.status = status

theorem extraction_gate_is_external_obligation :
    ModuleHasStatus ModuleName.extractionGate ClaimStatus.externalObligation := by
  unfold ModuleHasStatus
  refine ⟨
    { module := ModuleName.extractionGate
    , status := ClaimStatus.externalObligation
    , modeled := []
    , obligations := [ExternalObligation.realLanguageExtraction]
    }, ?_, rfl, rfl⟩
  simp [moduleClaimLedger]

theorem mini_source_extraction_is_verified :
    ModuleHasStatus ModuleName.miniSourceExtraction ClaimStatus.verified := by
  unfold ModuleHasStatus
  refine ⟨
    { module := ModuleName.miniSourceExtraction
    , status := ClaimStatus.verified
    , modeled := [ModeledSurface.miniSourceLanguage]
    , obligations := []
    }, ?_, rfl, rfl⟩
  simp [moduleClaimLedger]

theorem ci_gate_is_conditional :
    ModuleHasStatus ModuleName.ciGate ClaimStatus.conditional := by
  unfold ModuleHasStatus
  refine ⟨
    { module := ModuleName.ciGate
    , status := ClaimStatus.conditional
    , modeled := [ModeledSurface.ciTriage]
    , obligations :=
        [ExternalObligation.realLanguageExtraction,
          ExternalObligation.precisionEvaluation]
    }, ?_, rfl, rfl⟩
  simp [moduleClaimLedger]

end PcSastLean
