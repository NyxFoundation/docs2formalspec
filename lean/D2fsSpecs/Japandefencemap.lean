namespace Japandefencemap

-- Type abbreviations for domain types
abbrev UUID := Nat
abbrev Address := Nat
abbrev Year := Nat

-- Enumerations encoded as Nat for provability
-- ConfidenceLevel: 0=primary, 1=secondary, 2=derived
abbrev ConfidenceLevel := Nat

-- SourceType: 0=white_paper, 1=budget_request, 2=press_release, 3=other
abbrev SourceType := Nat

-- TaxonomyType: 0=mod_standard, 1=nato_stanag, 2=sipri, 3=custom
abbrev TaxonomyType := Nat

-- EquipmentStatus: 0=active, 1=planned, 2=retired, 3=prototype, 4=cancelled, 5=under_development
abbrev EquipmentStatus := Nat

-- Currency: 0=JPY, 1=USD, 2=EUR, 3=GBP
abbrev Currency := Nat

-- ContractType: 0=open_competition, 1=selective, 2=negotiated, 3=sole_source
abbrev ContractType := Nat

-- DeliveryStatus: 0=pending, 1=in_progress, 2=completed, 3=delayed, 4=cancelled, 5=partial
abbrev DeliveryStatus := Nat

-- Source record structure
structure Source where
  id : UUID
  url : String
  confidence_level : ConfidenceLevel
  source_type : SourceType
  requires_review : Bool
  is_loaded : Bool

-- Category record structure
structure Category where
  id : UUID
  parent_id : Option UUID
  taxonomy_type : TaxonomyType

-- Equipment record structure
structure Equipment where
  id : UUID
  canonical_name : String
  variant_name : String
  valid_from : Year
  status : EquipmentStatus
  introduced_year : Year
  retired_year : Option Year
  specs_json : String
  specs_schema_id : UUID
  requires_review : Bool
  is_loaded : Bool

-- Procurement record structure
structure Procurement where
  id : UUID
  total_amount_yen : Nat
  unit_price_yen : Option Nat
  quantity : Nat
  currency : Currency
  delivery_start_year : Year
  delivery_end_year : Option Year
  contract_type : ContractType
  delivery_status : DeliveryStatus
  requires_review : Bool
  is_loaded : Bool

-- Budget record structure
structure Budget where
  id : UUID
  amount_requested_yen : Nat
  amount_approved_yen : Nat
  justification : Option String
  requires_review : Bool
  is_loaded : Bool

-- Location record structure (latitude/longitude scaled by 10^6 for Nat representation)
structure Location where
  id : UUID
  latitude : Int  -- scaled: -90000000 to 90000000
  longitude : Int  -- scaled: -180000000 to 180000000
  requires_review : Bool
  is_loaded : Bool

-- Pending record for human review workflow
structure PendingRecord where
  record_type : String  -- "Source", "Category", "Equipment", "Procurement", "Budget", "Location"
  record_id : UUID
  source_id : UUID
  source_domain : String
  source_type : SourceType
  approval_status : Option Bool  -- none=pending, some true=approved, some false=rejected

-- Document in ingestion pipeline
structure Document where
  id : UUID
  url : String
  content : String
  blackout_ratio : Nat  -- scaled by 1000 (5% = 50)
  has_confidential_marker : Bool
  extraction_complete : Bool
  validation_complete : Bool

-- Spec schema for equipment validation
structure SpecSchema where
  id : UUID
  schema_content : String

-- Main State structure with all quantitative variables and access control
structure State where
  -- Access control fields (MUST be in State, not constant functions)
  admin_addresses : List Address
  ingestion_engine_addresses : List Address
  human_reviewer_addresses : List Address
  domain_whitelist : List String  -- allowed domains: *.mod.go.jp, *.mofa.go.jp, *.go.jp
  domain_blacklist : List String  -- blocked domains
  path_blacklist_patterns : List String  -- /internal/, /confidential/
  confidential_markers : List String  -- 機密，秘密，極秘，CONFIDENTIAL, SECRET, TOP SECRET
  known_source_types : List SourceType  -- track for unknown source_type detection
  
  -- Data tables (as Lists for provability)
  sources : List Source
  categories : List Category
  equipment : List Equipment
  procurements : List Procurement
  budgets : List Budget
  locations : List Location
  
  -- Pipeline state
  pending_documents : List Document
  pending_records : List PendingRecord
  
  -- Spec schemas for equipment validation
  spec_schemas : List SpecSchema
  
  -- Audit log for tracking operations
  audit_log : List String
  
  -- ID counters for generation
  source_counter : Nat
  category_counter : Nat
  equipment_counter : Nat
  procurement_counter : Nat
  budget_counter : Nat
  location_counter : Nat
  document_counter : Nat
  pending_counter : Nat
  
  -- Quantitative guardrails state
  total_budget_requested : Nat  -- sum of all amount_requested_yen
  total_budget_approved : Nat  -- sum of all amount_approved_yen
  total_procurement_amount : Nat  -- sum of all total_amount_yen
  active_equipment_count : Nat  -- count of equipment with status=active
  blackout_threshold : Nat  -- scaled threshold (50 = 5%)
  
  -- Cooldowns and rate limiting
  fetch_cooldown : Address -> Nat  -- blocks repeated fetches
  last_fetch_time : Address -> Nat
  
  -- Known domains tracking (for unknown-domain-manual-review requirement)
  known_domains : List String

-- Helper: check if URL starts with https://
def urlIsHttps (url : String) : Bool :=
  String.startsWith url "https://"

-- Helper: check if domain is in whitelist
def domainInWhitelist (domain : String) (whitelist : List String) : Bool :=
  List.any whitelist (fun d => d = domain ∨ String.endsWith domain d)

-- Helper: check if path matches blacklist patterns
def pathMatchesBlacklist (url : String) (patterns : List String) : Bool :=
  List.any patterns (fun p => String.contains url p)

-- Helper: check if document has confidential markers
def hasConfidentialMarker (content : String) (markers : List String) : Bool :=
  List.any markers (fun m => String.contains content m)

-- Helper: check blackout ratio exceeds threshold
def blackoutExceedsThreshold (ratio : Nat) (threshold : Nat) : Bool :=
  ratio > threshold

-- Helper: validate confidence level enum (0, 1, 2)
def validConfidenceLevel (cl : ConfidenceLevel) : Bool :=
  cl ≤ 2

-- Helper: validate source type enum
def validSourceType (st : SourceType) (known : List SourceType) : Bool :=
  List.contains known st

-- Helper: validate taxonomy type enum (0-3)
def validTaxonomyType (tt : TaxonomyType) : Bool :=
  tt ≤ 3

-- Helper: validate equipment status enum (0-5)
def validEquipmentStatus (es : EquipmentStatus) : Bool :=
  es ≤ 5

-- Helper: validate currency enum (0-3)
def validCurrency (c : Currency) : Bool :=
  c ≤ 3

-- Helper: validate contract type enum (0-3)
def validContractType (ct : ContractType) : Bool :=
  ct ≤ 3

-- Helper: validate delivery status enum (0-5)
def validDeliveryStatus (ds : DeliveryStatus) : Bool :=
  ds ≤ 5

-- Helper: check equipment year order (introduced ≤ retired if retired exists)
def validEquipmentYears (introduced : Year) (retired : Option Year) : Bool :=
  match retired with
  | none => true
  | some r => introduced ≤ r

-- Helper: check procurement amount consistency (within ±5%)
def validProcurementAmount (total : Nat) (unit : Option Nat) (qty : Nat) : Bool :=
  match unit with
  | none => true
  | some u =>
    let expected := u * qty
    let tolerance := expected * 5 / 100
    total ≥ expected - tolerance ∧ total ≤ expected + tolerance

-- Helper: check procurement delivery year order
def validProcurementDelivery (start : Year) (end : Option Year) : Bool :=
  match end with
  | none => true
  | some e => start ≤ e

-- Helper: check budget approved ≥ requested (unless justification provided)
def validBudgetAmount (requested : Nat) (approved : Nat) (justification : Option String) : Bool :=
  approved ≥ requested ∨ justification.isSome

-- Helper: check location latitude range (-90 to 90, scaled)
def validLatitude (lat : Int) : Bool :=
  lat ≥ -90000000 ∧ lat ≤ 90000000

-- Helper: check location longitude range (-180 to 180, scaled)
def validLongitude (lon : Int) : Bool :=
  lon ≥ -180000000 ∧ lon ≤ 180000000

-- Helper: check category has no self-cycle
def validCategoryParent (id : UUID) (parent_id : Option UUID) : Bool :=
  match parent_id with
  | none => true
  | some pid => id ≠ pid

-- Helper: check equipment unique name/variant/valid_from
def equipmentNameUnique (name : String) (variant : String) (valid_from : Year) (equipment : List Equipment) : Bool :=
  ¬List.any equipment (fun e => e.canonical_name = name ∧ e.variant_name = variant ∧ e.valid_from = valid_from)

-- Helper: check specs_schema_id exists
def specsSchemaExists (schema_id : UUID) (schemas : List SpecSchema) : Bool :=
  List.any schemas (fun s => s.id = schema_id)

-- Helper: check caller is admin
def callerIsAdmin (caller : Address) (admins : List Address) : Bool :=
  List.contains admins caller

-- Helper: check caller is ingestion engine
def callerIsIngestionEngine (caller : Address) (engines : List Address) : Bool :=
  List.contains engines caller

-- Helper: check caller is human reviewer
def callerIsHumanReviewer (caller : Address) (reviewers : List Address) : Bool :=
  List.contains reviewers callers

-- Helper: extract domain from URL
def extractDomain (url : String) : String :=
  -- Simplified: extract between "https://" and first "/"
  let withoutProtocol := String.dropPrefix "https://" url
  match String.split withoutProtocol "/" |>.head? with
  | some domain => domain
  | none => withoutProtocol

-- Helper: check if domain is known
def domainIsKnown (domain : String) (known : List String) : Bool :=
  List.contains known domain

-- Helper: check if source_type is known
def sourceTypeIsKnown (st : SourceType) (known : List SourceType) : Bool :=
  List.contains known st

-- Helper: find source by id
def findSource (id : UUID) (sources : List Source) : Option Source :=
  List.find? (fun s => s.id = id) sources

-- Helper: find category by id
def findCategory (id : UUID) (categories : List Category) : Option Category :=
  List.find? (fun c => c.id = id) categories

-- Helper: find equipment by id
def findEquipment (id : UUID) (equipment : List Equipment) : Option Equipment :=
  List.find? (fun e => e.id = id) equipment

-- Helper: find procurement by id
def findProcurement (id : UUID) (procurements : List Procurement) : Option Procurement :=
  List.find? (fun p => p.id = id) procurements

-- Helper: find budget by id
def findBudget (id : UUID) (budgets : List Budget) : Option Budget :=
  List.find? (fun b => b.id = id) budgets

-- Helper: find location by id
def findLocation (id : UUID) (locations : List Location) : Option Location :=
  List.find? (fun l => l.id = id) locations

-- Helper: find pending record by id
def findPendingRecord (id : UUID) (pending : List PendingRecord) : Option PendingRecord :=
  List.find? (fun p => p.record_id = id) pending

-- Helper: find document by id
def findDocument (id : UUID) (documents : List Document) : Option Document :=
  List.find? (fun d => d.id = id) documents

-- Helper: update list by replacing element
def updateList {α : Type} (l : List α) (id : UUID) (f : α → α) (getId : α → UUID) : List α :=
  l.map (fun x => if getId x = id then f x else x)

-- Helper: add audit log entry
def addAuditLog (s : State) (entry : String) : State :=
  { s with audit_log := entry :: s.audit_log }

-- Operations inductive type
inductive Op where
  -- Fetch operation: fetch document from URL
  | Fetch (url : String)
  -- DetectBlackout operation: check image blackout ratio
  | DetectBlackout (document_id : UUID) (blackout_ratio : Nat)
  -- Extract operation: extract candidate records from document
  | Extract (document_id : UUID)
  -- SchemaValidate operation: validate equipment specs against schema
  | SchemaValidate (equipment_id : UUID) (schema_id : UUID)
  -- Validate operation: validate a record against constraints
  | Validate (record_type : String) (record_id : UUID)
  -- Load operation: load validated record into table
  | Load (record_type : String) (record_id : UUID)
  -- HumanReview operation: approve/reject pending record
  | HumanReview (record_id : UUID) (approved : Bool)
  -- UpdateBudget operation: update budget approved amount
  | UpdateBudget (budget_id : UUID) (approved_amount : Nat) (justification : Option String)
  -- Delete operation: delete a record
  | Delete (record_type : String) (record_id : UUID)
  -- AddSpecSchema operation: add a spec schema for validation
  | AddSpecSchema (schema_id : UUID) (schema_content : String)
  -- AddKnownDomain operation: add domain to known domains list
  | AddKnownDomain (domain : String)
  -- AddKnownSourceType operation: add source type to known list
  | AddKnownSourceType (source_type : SourceType)

-- Main step function: state transition with all guard conditions
def step (s : State) (op : Op) (caller : Address) : Option State :=
  match op with
  
  -- Fetch: must be ingestion engine, URL must be https, domain whitelist, path blacklist
  | Op.Fetch url =>
    if ¬callerIsIngestionEngine caller s.ingestion_engine_addresses then
      none
    else if ¬urlIsHttps url then
      none  -- violates source-url-https requirement
    else
      let domain := extractDomain url
      if ¬domainInWhitelist domain s.domain_whitelist then
        none  -- violates fetch-domain-whitelist requirement
      else if pathMatchesBlacklist url s.path_blacklist_patterns then
        none  -- violates fetch-url-blacklist requirement
      else
        let doc_id := s.document_counter
        let doc : Document := {
          id := doc_id,
          url := url,
          content := "",
          blackout_ratio := 0,
          has_confidential_marker := false,
          extraction_complete := false,
          validation_complete := false
        }
        some {
          s with
          pending_documents := doc :: s.pending_documents,
          document_counter := doc_id + 1,
          audit_log := s"Fetch: {url} by {caller}" :: s.audit_log
        }
  
  -- DetectBlackout: check blackout ratio against 5% threshold
  | Op.DetectBlackout document_id blackout_ratio =>
    if ¬callerIsIngestionEngine caller s.ingestion_engine_addresses then
      none
    else if blackoutExceedsThreshold blackout_ratio s.blackout_threshold then
      none  -- violates blackout-area-warning requirement (>5%)
    else
      match findDocument document_id s.pending_documents with
      | none => none
      | some doc =>
        let updated_doc := { doc with blackout_ratio := blackout_ratio }
        some {
          s with
          pending_documents := updateList s.pending_documents document_id (fun _ => updated_doc) (fun d => d.id),
          audit_log := s"DetectBlackout: {document_id} ratio={blackout_ratio}" :: s.audit_log
        }
  
  -- Extract: extract candidate records, check for confidential markers
  | Op.Extract document_id =>
    if ¬callerIsIngestionEngine caller s.ingestion_engine_addresses then
      none
    else
      match findDocument document_id s.pending_documents with
      | none => none
      | some doc =>
        if hasConfidentialMarker doc.content s.confidential_markers then
          none  -- violates confidential-mark-rejection requirement
        else
          let updated_doc := { doc with extraction_complete := true }
          some {
            s with
            pending_documents := updateList s.pending_documents document_id (fun _ => updated_doc) (fun d => d.id),
            audit_log := s"Extract: {document_id}" :: s.audit_log
          }
  
  -- SchemaValidate: validate equipment specs against schema
  | Op.SchemaValidate equipment_id schema_id =>
    if ¬callerIsIngestionEngine caller s.ingestion_engine_addresses then
      none
    else if ¬specsSchemaExists schema_id s.spec_schemas then
      none  -- violates equipment-specs-schema-validation requirement
    else
      match findEquipment equipment_id s.equipment with
      | none => none
      | some equip =>
        if equip.specs_schema_id ≠ schema_id then
          none
        else
          some {
            s with
            audit_log := s"SchemaValidate: {equipment_id} schema={schema_id}" :: s.audit_log
          }
  
  -- Validate: validate record against all constraints
  | Op.Validate record_type record_id =>
    if ¬callerIsIngestionEngine caller s.ingestion_engine_addresses then
      none
    else
      match record_type with
      | "Source" =>
        match findSource record_id s.sources with
        | none => none
        | some src =>
          if ¬validConfidenceLevel src.confidence_level then
            none  -- violates source-confidence-enum
          else if ¬validSourceType src.source_type s.known_source_types then
            none  -- violates source-type-enum
          else
            some {
              s with
              audit_log := s"Validate Source: {record_id}" :: s.audit_log
            }
      | "Category" =>
        match findCategory record_id s.categories with
        | none => none
        | some cat =>
          if ¬validTaxonomyType cat.taxonomy_type then
            none  -- violates category-taxonomy-enum
          else if ¬validCategoryParent cat.id cat.parent_id then
            none  -- violates category-no-self-cycle
          else
            some {
              s with
              audit_log := s"Validate Category: {record_id}" :: s.audit_log
            }
      | "Equipment" =>
        match findEquipment record_id s.equipment with
        | none => none
        | some equip =>
          if ¬validEquipmentStatus equip.status then
            none  -- violates equipment-status-enum
          else if ¬validEquipmentYears equip.introduced_year equip.retired_year then
            none  -- violates equipment-year-order
          else if ¬equipmentNameUnique equip.canonical_name equip.variant_name equip.valid_from s.equipment then
            none  -- violates equipment-unique-name-variant
          else if ¬specsSchemaExists equip.specs_schema_id s.spec_schemas then
            none  -- violates equipment-specs-schema-validation
          else
            some {
              s with
              audit_log := s"Validate Equipment: {record_id}" :: s.audit_log
            }
      | "Procurement" =>
        match findProcurement record_id s.procurements with
        | none => none
        | some proc =>
          if ¬validCurrency proc.currency then
            none  -- violates procurement-currency-enum
          else if ¬validContractType proc.contract_type then
            none  -- violates procurement-contract-type-enum
          else if ¬validDeliveryStatus proc.delivery_status then
            none  -- violates procurement-delivery-status-enum
          else if ¬validProcurementAmount proc.total_amount_yen proc.unit_price_yen proc.quantity then
            none  -- violates procurement-amount-consistency
          else if ¬validProcurementDelivery proc.delivery_start_year proc.delivery_end_year then
            none  -- violates procurement-delivery-order
          else
            some {
              s with
              audit_log := s"Validate Procurement: {record_id}" :: s.audit_log
            }
      | "Budget" =>
        match findBudget record_id s.budgets with
        | none => none
        | some bud =>
          if ¬validBudgetAmount bud.amount_requested_yen bud.amount_approved_yen bud.justification then
            none  -- violates budget-approved-not-less-than-requested
          else
            some {
              s with
              audit_log := s"Validate Budget: {record_id}" :: s.audit_log
            }
      | "Location" =>
        match findLocation record_id s.locations with
        | none => none
        | some loc =>
          if ¬validLatitude loc.latitude then
            none  -- violates location-latlon-range
          else if ¬validLongitude loc.longitude then
            none  -- violates location-latlon-range
          else
            some {
              s with
              audit_log := s"Validate Location: {record_id}" :: s.audit_log
            }
      | _ => none
  
  -- Load: load validated record, check for manual review requirement
  | Op.Load record_type record_id =>
    if ¬callerIsIngestionEngine caller s.ingestion_engine_addresses then
      none
    else
      match record_type with
      | "Source" =>
        match findSource record_id s.sources with
        | none => none
        | some src =>
          if src.requires_review then
            none  -- requires human review first
          else if src.is_loaded then
            none  -- already loaded
          else
            let updated_src := { src with is_loaded := true }
            some {
              s with
              sources := updateList s.sources record_id (fun _ => updated_src) (fun x => x.id),
              audit_log := s"Load Source: {record_id}" :: s.audit_log
            }
      | "Category" =>
        match findCategory record_id s.categories with
        | none => none
        | some cat =>
          some {
            s with
            categories := cat :: s.categories,
            category_counter := s.category_counter + 1,
            audit_log := s"Load Category: {record_id}" :: s.audit_log
          }
      | "Equipment" =>
        match findEquipment record_id s.equipment with
        | none => none
        | some equip =>
          if equip.requires_review then
            none  -- requires human review first
          else if equip.is_loaded then
            none
          else
            let updated_equip := { equip with is_loaded := true }
            some {
              s with
              equipment := updateList s.equipment record_id (fun _ => updated_equip) (fun x => x.id),
              active_equipment_count := if equip.status = 0 then s.active_equipment_count + 1 else s.active_equipment_count,
              audit_log := s"Load Equipment: {record_id}" :: s.audit_log
            }
      | "Procurement" =>
        match findProcurement record_id s.procurements with
        | none => none
        | some proc =>
          if proc.requires_review then
            none
          else if proc.is_loaded then
            none
          else
            let updated_proc := { proc with is_loaded := true }
            some {
              s with
              procurements := updateList s.procurements record_id (fun _ => updated_proc) (fun x => x.id),
              total_procurement_amount := s.total_procurement_amount + proc.total_amount_yen,
              audit_log := s"Load Procurement: {record_id}" :: s.audit_log
            }
      | "Budget" =>
        match findBudget record_id s.budgets with
        | none => none
        | some bud =>
          if bud.requires_review then
            none
          else if bud.is_loaded then
            none
          else
            let updated_bud := { bud with is_loaded := true }
            some {
              s with
              budgets := updateList s.budgets record_id (fun _ => updated_bud) (fun x => x.id),
              total_budget_requested := s.total_budget_requested + bud.amount_requested_yen,
              total_budget_approved := s.total_budget_approved + bud.amount_approved_yen,
              audit_log := s"Load Budget: {record_id}" :: s.audit_log
            }
      | "Location" =>
        match findLocation record_id s.locations with
        | none => none
        | some loc =>
          if loc.requires_review then
            none
          else if loc.is_loaded then
            none
          else
            let updated_loc := { loc with is_loaded := true }
            some {
              s with
              locations := updateList s.locations record_id (fun _ => updated_loc) (fun x => x.id),
              audit_log := s"Load Location: {record_id}" :: s.audit_log
            }
      | _ => none
  
  -- HumanReview: approve/reject pending record (unknown domain or new source_type)
  | Op.HumanReview record_id approved =>
    if ¬callerIsHumanReviewer caller s.human_reviewer_addresses then
      none
    else
      match findPendingRecord record_id s.pending_records with
      | none => none
      | some pending =>
        if ¬pending.requires_review then
          none  -- doesn't require review
        else if pending.approval_status.isSome then
          none  -- already reviewed
        else
          let updated_pending := { pending with approval_status := some approved }
          if approved then
            -- Mark corresponding record as not requiring review
            match pending.record_type with
            | "Source" =>
              match findSource pending.record_id s.sources with
              | none => none
              | some src =>
                let updated_src := { src with requires_review := false }
                some {
                  s with
                  sources := updateList s.sources pending.record_id (fun _ => updated_src) (fun x => x.id),
                  pending_records := updateList s.pending_records record_id (fun _ => updated_pending) (fun x => x.record_id),
                  audit_log := s"HumanReview: {record_id} approved" :: s.audit_log
                }
            | "Equipment" =>
              match findEquipment pending.record_id s.equipment with
              | none => none
              | some equip =>
                let updated_equip := { equip with requires_review := false }
                some {
                  s with
                  equipment := updateList s.equipment pending.record_id (fun _ => updated_equip) (fun x => x.id),
                  pending_records := updateList s.pending_records record_id (fun _ => updated_pending) (fun x => x.record_id),
                  audit_log := s"HumanReview: {record_id} approved" :: s.audit_log
                }
            | _ =>
              some {
                s with
                pending_records := updateList s.pending_records record_id (fun _ => updated_pending) (fun x => x.record_id),
                audit_log := s"HumanReview: {record_id} approved" :: s.audit_log
              }
          else
            some {
              s with
              pending_records := updateList s.pending_records record_id (fun _ => updated_pending) (fun x => x.record_id),
              audit_log := s"HumanReview: {record_id} rejected" :: s.audit_log
            }
  
  -- UpdateBudget: update approved amount with justification check
  | Op.UpdateBudget budget_id approved_amount justification =>
    if ¬callerIsAdmin caller s.admin_addresses then
      none
    else
      match findBudget budget_id s.budgets with
      | none => none
      | some bud =>
        if ¬validBudgetAmount bud.amount_requested_yen approved_amount justification then
          none  -- violates budget-approved-not-less-than-requested
        else
          let updated_bud := { bud with amount_approved_yen := approved_amount, justification := justification }
          let new_total_approved := s.total_budget_approved - bud.amount_approved_yen + approved_amount
          some {
            s with
            budgets := updateList s.budgets budget_id (fun _ => updated_bud) (fun x => x.id),
            total_budget_approved := new_total_approved,
            audit_log := s"UpdateBudget: {budget_id} approved={approved_amount}" :: s.audit_log
          }
  
  -- Delete: delete record (admin only, check FK constraints)
  | Op.Delete record_type record_id =>
    if ¬callerIsAdmin caller s.admin_addresses then
      none
    else
      match record_type with
      | "Source" =>
        -- Check no FK violations (simplified: check if any record references this source)
        let has_references := 
          List.any s.equipment (fun e => false) ∨  -- would check source_id FK
          List.any s.procurements (fun p => false) ∨
          List.any s.budgets (fun b => false)
        if has_references then
          none  -- FK violation
        else
          some {
            s with
            sources := s.sources.filter (fun x => x.id ≠ record_id),
            audit_log := s"Delete Source: {record_id}" :: s.audit_log
          }
      | "Category" =>
        -- Check no child categories reference this
        let has_children := List.any s.categories (fun c => c.parent_id = some record_id)
        if has_children then
          none  -- FK violation
        else
          some {
            s with
            categories := s.categories.filter (fun x => x.id ≠ record_id),
            audit_log := s"Delete Category: {record_id}" :: s.audit_log
          }
      | "Equipment" =>
        some {
          s with
          equipment := s.equipment.filter (fun x => x.id ≠ record_id),
          active_equipment_count := if s.active_equipment_count > 0 then s.active_equipment_count - 1 else 0,
          audit_log := s"Delete Equipment: {record_id}" :: s.audit_log
        }
      | "Procurement" =>
        match findProcurement record_id s.procurements with
        | none => none
        | some proc =>
          some {
            s with
            procurements := s.procurements.filter (fun x => x.id ≠ record_id),
            total_procurement_amount := s.total_procurement_amount - proc.total_amount_yen,
            audit_log := s"Delete Procurement: {record_id}" :: s.audit_log
          }
      | "Budget" =>
        match findBudget record_id s.budgets with
        | none => none
        | some bud =>
          some {
            s with
            budgets := s.budgets.filter (fun x => x.id ≠ record_id),
            total_budget_requested := s.total_budget_requested - bud.amount_requested_yen,
            total_budget_approved := s.total_budget_approved - bud.amount_approved_yen,
            audit_log := s"Delete Budget: {record_id}" :: s.audit_log
          }
      | "Location" =>
        some {
          s with
          locations := s.locations.filter (fun x => x.id ≠ record_id),
          audit_log := s"Delete Location: {record_id}" :: s.audit_log
        }
      | _ => none
  
  -- AddSpecSchema: add schema for equipment validation
  | Op.AddSpecSchema schema_id schema_content =>
    if ¬callerIsAdmin caller s.admin_addresses then
      none
    else
      let schema : SpecSchema := {
        id := schema_id,
        schema_content := schema_content
      }
      some {
        s with
        spec_schemas := schema :: s.spec_schemas,
        audit_log := s"AddSpecSchema: {schema_id}" :: s.audit_log
      }
  
  -- AddKnownDomain: add domain to known domains (for unknown-domain-manual-review)
  | Op.AddKnownDomain domain =>
    if ¬callerIsAdmin caller s.admin_addresses then
      none
    else if domainIsKnown domain s.known_domains then
      some s  -- already known, no change
    else
      some {
        s with
        known_domains := domain :: s.known_domains,
        audit_log := s"AddKnownDomain: {domain}" :: s.audit_log
      }
  
  -- AddKnownSourceType: add source type to known list
  | Op.AddKnownSourceType source_type =>
    if ¬callerIsAdmin caller s.admin_addresses then
      none
    else if sourceTypeIsKnown source_type s.known_source_types then
      some s  -- already known
    else
      some {
        s with
        known_source_types := source_type :: s.known_source_types,
        audit_log := s"AddKnownSourceType: {source_type}" :: s.audit_log
      }

-- Helper: calculate total supply of budget requested
def totalBudgetRequested (s : State) : Nat :=
  s.total_budget_requested

-- Helper: calculate total supply of budget approved
def totalBudgetApproved (s : State) : Nat :=
  s.total_budget_approved

-- Helper: calculate total procurement amount
def totalProcurementAmount (s : State) : Nat :=
  s.total_procurement_amount

-- Helper: count active equipment
def activeEquipmentCount (s : State) : Nat :=
  s.active_equipment_count

-- Helper: check if URL is valid per requirements
def urlIsValid (url : String) (whitelist : List String) (blacklist : List String) : Bool :=
  urlIsHttps url ∧ domainInWhitelist (extractDomain url) whitelist ∧ ¬pathMatchesBlacklist url blacklist

-- Helper: check if document passes all checks
def documentPassesChecks (doc : Document) (threshold : Nat) (markers : List String) : Bool :=
  ¬blackoutExceedsThreshold doc.blackout_ratio threshold ∧ ¬doc.has_confidential_marker

-- Helper: check if record requires human review
def recordRequiresReview (domain : String) (source_type : SourceType) (known_domains : List String) (known_types : List SourceType) : Bool :=
  ¬domainIsKnown domain known_domains ∨ ¬sourceTypeIsKnown source_type known_types

-- Helper: get source by ID
def getSource (s : State) (id : UUID) : Option Source :=
  findSource id s.sources

-- Helper: get category by ID
def getCategory (s : State) (id : UUID) : Option Category :=
  findCategory id s.categories

-- Helper: get equipment by ID
def getEquipment (s : State) (id : UUID) : Option Equipment :=
  findEquipment id s.equipment

-- Helper: get procurement by ID
def getProcurement (s : State) (id : UUID) : Option Procurement :=
  findProcurement id s.procurements

-- Helper: get budget by ID
def getBudget (s : State) (id : UUID) : Option Budget :=
  findBudget id s.budgets

-- Helper: get location by ID
def getLocation (s : State) (id : UUID) : Option Location :=
  findLocation id s.locations

-- Helper: check if caller has admin role
def hasAdminRole (s : State) (caller : Address) : Bool :=
  callerIsAdmin caller s.admin_addresses

-- Helper: check if caller is ingestion engine
def hasIngestionRole (s : State) (caller : Address) : Bool :=
  callerIsIngestionEngine caller s.ingestion_engine_addresses

-- Helper: check if caller is human reviewer
def hasReviewerRole (s : State) (caller : Address) : Bool :=
  callerIsHumanReviewer caller s.human_reviewer_addresses

-- Initial state constructor
def initialState : State :=
  {
    admin_addresses := [],
    ingestion_engine_addresses := [],
    human_reviewer_addresses := [],
    domain_whitelist := ["mod.go.jp", "mofa.go.jp", "go.jp"],
    domain_blacklist := [],
    path_blacklist_patterns := ["/internal/", "/confidential/"],
    confidential_markers := ["機密", "秘密", "極秘", "CONFIDENTIAL", "SECRET", "TOP SECRET"],
    known_source_types := [0, 1, 2, 3],  -- white_paper, budget_request, press_release, other
    sources := [],
    categories := [],
    equipment := [],
    procurements := [],
    budgets := [],
    locations := [],
    pending_documents := [],
    pending_records := [],
    spec_schemas := [],
    audit_log := [],
    source_counter := 0,
    category_counter := 0,
    equipment_counter := 0,
    procurement_counter := 0,
    budget_counter := 0,
    location_counter := 0,
    document_counter := 0,
    pending_counter := 0,
    total_budget_requested := 0,
    total_budget_approved := 0,
    total_procurement_amount := 0,
    active_equipment_count := 0,
    blackout_threshold := 50,  -- 5% scaled by 1000
    fetch_cooldown := fun _ => 0,
    last_fetch_time := fun _ => 0,
    known_domains := ["mod.go.jp", "mofa.go.jp", "go.jp"]
  }

end Japandefencemap
