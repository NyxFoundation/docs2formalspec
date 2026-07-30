# JapanDefenceMap Specification  

**Status:** Draft Standard (Work in Progress)  

---  

## 1. Introduction  

JapanDefenceMap (JDM) is a data‑integration platform that aggregates, validates, and publishes information about Japan’s defence‑related equipment, procurement, budgets, and source documentation. The system ingests documents from a limited set of government domains, extracts structured data, and stores it in a relational database that enforces strict data‑quality and security guardrails.  

The purpose of this specification is to define, in a **RFC‑2119‑conformant** manner, the mandatory constraints, invariants, and operational guardrails that an implementation of JDM must satisfy. The scope covers:  

* Validation of source metadata (URLs, confidence levels, types).  
* Taxonomy and hierarchy rules for categories.  
* Integrity constraints for equipment, procurement, budget, and location data.  
* Access‑control policies for fetching external documents.  
* Failure‑handling rules for confidential content, black‑out detection, and unknown sources.  

---  

## 2. Terminology  

The following definitions use the key words **MUST**, **MUST NOT**, **REQUIRED**, **SHALL**, **SHALL NOT**, **SHOULD**, **SHOULD NOT**, **RECOMMENDED**, **MAY**, and **OPTIONAL** as described in **RFC 2119**.  

* **MUST** – an absolute requirement of the specification.  
* **MUST NOT** – a prohibition.  
* **SHALL** – equivalent to MUST.  
* **SHALL NOT** – equivalent to MUST NOT.  
* **SHOULD** – recommended but not mandatory.  
* **SHOULD NOT** – discouraged but not prohibited.  
* **MAY** – optional.  

### Domain‑specific terms  

| Term | Definition |
|------|------------|
| **source** | A record describing the origin of a piece of data (e.g., a white paper, press release). |
| **source_id** | UUID that uniquely identifies a source; required on every record that references provenance. |
| **category** | A hierarchical classification node for equipment or procurement items. |
| **taxonomy_type** | The classification scheme used for a category (e.g., `mod_standard`). |
| **equipment** | A defence asset (e.g., aircraft, ship) with attributes such as `canonical_name`, `variant_name`, `status`, and `specs_json`. |
| **procurement** | A contract record describing acquisition of equipment, including financial fields and delivery schedule. |
| **budget** | A financial plan record containing `amount_requested_yen` and `amount_approved_yen`. |
| **location** | Geographic coordinates (`latitude`, `longitude`) associated with a facility or deployment. |
| **fetch stage** | The phase where external URLs are retrieved before extraction. |
| **extract stage** | The phase where document content is parsed and transformed into structured records. |
| **load stage** | The phase where validated records are persisted to the database. |
| **black‑out area** | Portion of an OCR‑processed image that is completely black, indicating redacted content. |

---  

## 3. System Model  

### 3.1 Actors  

| Actor | Role |
|-------|------|
| **Ingestion Engine** | Retrieves documents, runs OCR, extracts structured data, and invokes validation logic. |
| **Human Reviewer** | Performs manual review when required (e.g., unknown domains, new `source_type`). |
| **Database** | Stores all normalized tables (`source`, `category`, `equipment`, `procurement`, `budget`, `location`, …) and enforces constraints. |
| **Policy Service** | Supplies JSON schemas for `equipment.specs_json` validation. |
| **Security Guard** | Applies domain whitelist/blacklist, confidential‑marker detection, and black‑out thresholds. |

### 3.2 State Variables  

* `source.id : UUID` – primary key of a source record.  
* `source.url : TEXT` – URL of the source document.  
* `source.confidence_level : ENUM('primary','secondary','derived')`.  
* `source.source_type : ENUM(…see §2)` .  
* `category.id : UUID`, `category.parent_id : UUID?`, `category.taxonomy_type : ENUM('mod_standard','nato_stanag','sipri','custom')`.  
* `equipment.id : UUID`, `equipment.canonical_name : TEXT`, `equipment.variant_name : TEXT`, `equipment.valid_from : DATE`, `equipment.status : ENUM('active','planned','retired','prototype','cancelled','under_development')`, `equipment.introduced_year : INT`, `equipment.retired_year : INT?`, `equipment.specs_json : JSONB`, `equipment.specs_schema_id : UUID`.  
* `procurement.id : UUID`, `procurement.total_amount_yen : NUMERIC`, `procurement.unit_price_yen : NUMERIC?`, `procurement.quantity : NUMERIC`, `procurement.currency : ENUM('JPY','USD','EUR','GBP')`, `procurement.delivery_start_year : INT`, `procurement.delivery_end_year : INT?`, `procurement.contract_type : ENUM('open_competition','selective','negotiated','sole_source')`, `procurement.delivery_status : ENUM('pending','in_progress','completed','delayed','cancelled','partial')`.  
* `budget.id : UUID`, `budget.amount_requested_yen : NUMERIC`, `budget.amount_approved_yen : NUMERIC`.  
* `location.id : UUID`, `location.latitude : NUMERIC`, `location.longitude : NUMERIC`.  

### 3.3 Operations  

| Operation | Description |
|-----------|-------------|
| **Fetch(URL)** | Retrieve a document; MUST enforce domain whitelist and URL blacklist (see §6). |
| **Extract(Document)** | Run OCR, parse, and produce candidate records; MUST abort on confidential markers (see §7). |
| **Validate(Record)** | Apply all state, arithmetic, economic, and access‑control constraints; MUST reject non‑conforming records. |
| **Load(ValidatedRecord)** | Persist the record; MUST require manual review for unknown domains or new `source_type`. |
| **SchemaValidate(specs_json, specs_schema_id)** | Verify JSON conforms to the referenced schema; MUST be performed on INSERT/UPDATE of equipment. |
| **DetectBlackout(Image)** | Compute black‑out area ratio; MUST halt ingestion if > 5 %. |

---  

## 4. State Requirements  

### REQ‑source-url-https  

> **The system MUST ensure that every source URL starts with https://.**  

*All source records must have a `url` that matches the regular expression `^https://`. The database enforces this via a CHECK constraint.*  

### REQ‑source-confidence-enum  

> **The system MUST enforce that each source's confidence_level is one of 'primary', 'secondary', or 'derived'.**  

*The `confidence_level` column is defined with a CHECK constraint limiting values to the three enumerated strings.*  

### REQ‑source-type-enum  

> **The system MUST restrict source_type values to the defined enumeration.**  

*`source_type` is a VARCHAR(50) column whose allowed values are explicitly listed in the design (e.g., `white_paper`, `budget_request`, …).*  

### REQ‑source-id-mandatory  

> **The system MUST require a non‑null source_id for every record in all tables.**  

*All foreign‑key references to `source` are declared `NOT NULL`, guaranteeing provenance for every stored entity.*  

### REQ‑category-no-self-cycle  

> **The system MUST prevent a category from referencing itself as its parent.**  

*A CHECK constraint (or trigger) enforces `parent_id ≠ id` to avoid self‑referential cycles.*  

### REQ‑category-taxonomy-enum  

> **The system MUST restrict category taxonomy_type to one of 'mod_standard', 'nato_stanag', 'sipri', or 'custom'.**  

*The `taxonomy_type` column is constrained to the four enumerated values.*  

### REQ‑equipment-status-enum  

> **The system MUST limit equipment status to the set {'active','planned','retired','prototype','cancelled','under_development'}.**  

*Implemented via a CHECK constraint on the `status` column.*  

### REQ‑equipment-unique-name-variant  

> **The system MUST enforce uniqueness of (canonical_name, variant_name, valid_from) across equipment records.**  

*A UNIQUE constraint prevents duplicate time‑stamped name/variant combinations.*  

### REQ‑equipment-specs-schema-validation  

> **The system MUST validate that equipment.specs_json conforms to the JSON schema referenced by its specs_schema_id.**  

*Validation occurs at INSERT/UPDATE time, either via a trigger or application logic that loads the schema from `equipment_spec_schema` and checks `specs_json`.*  

### REQ‑location-latlon-range  

> **The system MUST enforce that location.latitude is between -90 and 90 and location.longitude is between -180 and 180.**  

*Application‑layer validation (or database CHECK) guarantees geographic coordinates are within valid ranges.*  

---  

## 5. Arithmetic Requirements  

### REQ‑equipment-year-order  

> **The system MUST ensure that an equipment's introduced_year is less than or equal to its retired_year, unless retired_year is null.**  

*CHECK constraint `retired_year IS NULL OR introduced_year <= retired_year` enforces temporal ordering.*  

### REQ‑procurement-amount-consistency  

> **The system MUST verify that procurement.total_amount_yen is within ±5 % of quantity × unit_price_yen, unless unit_price_yen is null.**  

*CHECK constraint validates `total_amount_yen` lies between `0.95 * unit_price_yen * quantity` and `1.05 * unit_price_yen * quantity` when `unit_price_yen` is present.*  

### REQ‑procurement-delivery-order  

> **The system MUST ensure that procurement.delivery_end_year is null or not earlier than delivery_start_year.**  

*CHECK constraint `delivery_end_year IS NULL OR delivery_start_year <= delivery_end_year` enforces chronological consistency.*  

---  

## 6. Economic Requirements  

### REQ‑budget-approved-not-less-than-requested  

> **The system MUST ensure that budget.amount_approved_yen is greater than or equal to budget.amount_requested_yen, except where documented reductions apply.**  

*Business‑logic validation (e.g., during budget record creation) must compare the two fields and allow an exception only when an explicit reduction justification is attached.*  

---  

## 7. Access‑Control Requirements  

### REQ‑fetch-domain-whitelist  

> **The system MUST fetch documents only from domains matching *.mod.go.jp, *.mofa.go.jp, or *.go.jp.**  

*The fetch component validates the hostname of every URL against the whitelist before initiating a network request.*  

### REQ‑fetch-url-blacklist  

> **The system MUST reject any URL whose path matches /internal/ or /confidential/ patterns.**  

*Path‑level filtering is applied after domain validation; matching URLs are discarded with an error.*  

### REQ‑unknown-domain-manual-review  

> **The system MUST require manual review before loading data from an unknown domain or a newly introduced source_type.**  

*When a URL’s domain is not present in the whitelist or a `source_type` value is not among the pre‑approved list, the ingestion pipeline pauses and flags the record for human verification.*  

---  

## 8. Failure Requirements  

### REQ‑confidential-mark-rejection  

> **The system MUST abort processing of any document that contains any of the confidential markers '機密', '秘密', '極秘', 'CONFIDENTIAL', 'SECRET', or 'TOP SECRET'.**  

*During the extract stage, the content is scanned for these strings; detection triggers immediate pipeline termination for that document.*  

### REQ‑blackout-area-warning  

> **The system MUST issue a warning and halt ingestion when the proportion of blacked‑out area in an OCR‑processed image exceeds 5 %.**  

*The OCR post‑processor computes the black‑out ratio; exceeding the 5 % threshold generates a warning and stops further processing of the associated document.*  

---  

## 9. Security Considerations  

JapanDefenceMap processes publicly available government documents that may contain sensitive or classified material. The specification enforces a defense‑in‑depth posture:  

* **Transport security** – All source URLs must use HTTPS (REQ‑source-url-https).  
* **Domain restriction** – Only approved government domains are reachable (REQ‑fetch-domain-whitelist).  
* **Content sanitisation** – Confidential markers cause immediate abort (REQ‑confidential-mark-rejection).  
* **Redaction detection** – Excessive black‑out areas halt ingestion (REQ‑blackout-area-warning).  
* **Manual oversight** – Unknown domains or new source types require human review (REQ‑unknown-domain-manual-review).  

Implementations should also consider rate‑limiting, TLS certificate validation, and logging of all guardrail violations for auditability.  

---  

## 10. References  

* DESIGN.md – JapanDefenceMap design document (source of all constraints).  
  * File path: `/tmp/japan-defence-map/docs/DESIGN.md`  

* RFC 2119 – *Key words for use in RFCs to Indicate Requirement Levels*.  

---  

*End of Specification*