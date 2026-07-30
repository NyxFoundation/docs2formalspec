## JapanDefenceMap – Formal State‑Transition Model  

| **Category** | **Item** | **Type / Enum** | **Meaning** |
|--------------|----------|----------------|-------------|
| **Source** | `id` | UUID (PK) | Unique provenance identifier |
| | `url` | TEXT (must match `^https://`) | HTTPS location of the original document |
| | `confidence_level` | ENUM{primary, secondary, derived} | Trust tier of the source |
| | `source_type` | ENUM{white_paper, budget_request, press_release, …} | Classification of the document |
| **Category** | `id` | UUID (PK) | Node identifier in the taxonomy |
| | `parent_id` | UUID? (FK→Category.id) | Parent node; `NULL` for root |
| | `taxonomy_type` | ENUM{mod_standard, nato_stanag, sipri, custom} | Scheme used for this node |
| **Equipment** | `id` | UUID (PK) | Asset identifier |
| | `canonical_name` | TEXT | Official name (e.g., “F‑15”) |
| | `variant_name` | TEXT | Sub‑type (e.g., “ECR”) |
| | `valid_from` | DATE | First day the record is valid |
| | `status` | ENUM{active, planned, retired, prototype, cancelled, under_development} | Lifecycle state |
| | `introduced_year` | INT (1900‑2100) | Year first entered service |
| | `retired_year` | INT? (≥ introduced_year) | Year withdrawn, if any |
| | `specs_json` | JSONB | Free‑form technical specs |
| | `specs_schema_id` | UUID (FK→SpecSchema.id) | Schema that `specs_json` must obey |
| **Procurement** | `id` | UUID (PK) | Contract identifier |
| | `total_amount_yen` | NUMERIC(15,2) | Contract value in JPY |
| | `unit_price_yen` | NUMERIC(15,2)? | Price per unit, if disclosed |
| | `quantity` | NUMERIC(12,2) | Number of units |
| | `currency` | ENUM{JPY, USD, EUR, GBP} | Currency of the contract |
| | `delivery_start_year` | INT (≥ 2000) | Planned start of delivery |
| | `delivery_end_year` | INT? (≥ delivery_start_year) | Planned end of delivery |
| | `contract_type` | ENUM{open_competition, selective, negotiated, sole_source} | Procurement regime |
| | `delivery_status` | ENUM{pending, in_progress, completed, delayed, cancelled, partial} | Current progress |
| **Budget** | `id` | UUID (PK) | Budget line identifier |
| | `amount_requested_yen` | NUMERIC(15,2) | Requested funds |
| | `amount_approved_yen` | NUMERIC(15,2) | Approved funds (≥ requested unless justification) |
| **Location** | `id` | UUID (PK) | Facility identifier |
| | `latitude` | NUMERIC(8,6) (‑90 … +90) | Geographic latitude |
| | `longitude` | NUMERIC(9,6) (‑180 … +180) | Geographic longitude |

### Actors
| Actor | Role |
|-------|------|
| **IngestionEngine** | Executes *Fetch → Extract → Validate → Load* pipeline |
| **HumanReviewer** | Approves records flagged for unknown domains or new `source_type` |
| **Database** | Persists all tables and enforces declarative constraints |
| **PolicyService** | Supplies JSON‑Schema objects referenced by `specs_schema_id` |
| **SecurityGuard** | Performs domain whitelist/blacklist checks, confidential‑marker detection, blackout‑area analysis |

### Operations (state‑transition primitives)

| Operation | Inputs | Preconditions (must hold before) | Effects (state change) |
|----------|--------|----------------------------------|------------------------|
| **Fetch(url)** | `url: TEXT` | `url` matches whitelist `*.mod.go.jp ∨ *.mofa.go.jp ∨ *.go.jp` **and** does **not** match blacklist `/internal/|/confidential/` | Returns `Document` (binary) and creates a **Source** row with `url` and generated `id` |
| **DetectBlackout(image)** | `image: raster` | Image is OCR‑ready | Computes `blackout_ratio`; if `> 0.05` → abort pipeline, else no state change |
| **Extract(document)** | `Document` | Document passed `DetectBlackout` and contains **no** confidential markers (`機密|秘密|極秘|CONFIDENTIAL|SECRET|TOP SECRET`) | Emits candidate records for `Category`, `Equipment`, `Procurement`, `Budget`, `Location` (still transient) |
| **SchemaValidate(specs_json, specs_schema_id)** | `JSON`, `UUID` | `specs_schema_id` exists in `SpecSchema` table | Returns *valid* / *invalid*; on *invalid* the candidate `Equipment` record is rejected |
| **Validate(record)** | Any candidate record | All **REQ‑** constraints applicable to the record’s table are satisfied (e.g., enum membership, numeric ranges, arithmetic checks) | Marks record as **Validated**; otherwise produces a rejection reason |
| **Load(validated_record)** | `Validated` record | If record originates from an **unknown domain** or uses a **new `source_type`**, a flag `requires_review = TRUE` is set and the operation pauses until **HumanReviewer** approves | Inserts the record into the corresponding table; sets `source_id` foreign key; updates audit log |
| **HumanReview(record)** | `record` with `requires_review = TRUE` | Human reviewer has examined the source and set `approval = TRUE` | Clears `requires_review`; triggers `Load` to complete insertion |
| **UpdateBudget(budget_id, approved_amount, justification?)** | `budget_id`, `approved_amount` | `approved_amount ≥ amount_requested_yen` **unless** a non‑null `justification` is supplied | Updates `amount_approved_yen`; logs justification if exception used |
| **Delete(id, table)** | `id`, target `table` name | Caller holds appropriate admin role; no foreign‑key violations would be created | Removes the row; cascades or restricts per DB FK rules |

*All operations are atomic at the database transaction level; any violation of a precondition aborts the transaction and rolls back.*  

---  

**Quantitative Guardrails**  

* HTTPS‑only URLs (`^https://`).  
* Black‑out area ≤ 5 % (0.05).  
* Procurement total amount must be within ±5 % of `quantity × unit_price_yen`.  
* Latitude ∈ [‑90, +90]; Longitude ∈ [‑180, +180].  
* Introduced ≤ Retired (if retired not null).  

These variables, actors, and operations together define the complete state‑transition model required by the JapanDefenceMap specification.