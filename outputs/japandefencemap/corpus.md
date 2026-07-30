# DESIGN.md
_source: /tmp/japan-defence-map/docs/DESIGN.md_

# 防衛省装備品3D可視化マップ — 全体設計書 v2.0

> Issue: grandchildrice/life#30
> 作成日: 2026-07-22
> 更新日: 2026-07-22（セルフレビュー後の再設計）
> ステータス: 設計完了 → 実装待ち

---

## 1. 設計のゴールと前提

### ゴール
防衛省が公開している一次資料（入札情報、防衛大綱、予算書、防衛白書等）を構造化し、装備品（武器・車両・艦船・航空機等）の時系列・金額・メーカー・部品関係をインタラクティブな3Dマップで可視化する。

### 前提制約
- **公開情報のみを対象とする** — 機密情報は一切扱わない
- **一次資料に依拠** — 二次解説ではなく、防衛省/防衛装備庁/外務省の公開文書をソースとする
- **継続的に更新可能** — 毎年度の予算・調達情報の追加に対応する構造
- **検証可能性** — 各データポイントがどの一次資料のどのページに由来するかを追跡可能にする

---

## 2. 全体アーキテクチャ（レイヤード構成）

```
┌─────────────────────────────────────────────────────────────┐
│  レイヤー4: 可視化・インタラクション層 (Visually / Three.js)  │
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────────────────┐ │
│  │ 3D装備品マップ │ │ 予算フロー  │ │ 時系列アニメーション       │ │
│  │ (Three.js)   │ │ (Network)   │ │ (Temporal Playback)     │ │
│  └─────────────┘ └─────────────┘ └─────────────────────────┘ │
├─────────────────────────────────────────────────────────────┤
│  レイヤー3: ナレッジグラフ・推論層 (Graph DB + Python)        │
│  - エンティティ間関係の構造化                                  │
│  - 時系列データの補間・推論                                    │
│  - サプライチェーンのネットワーク構築                           │
├─────────────────────────────────────────────────────────────┤
│  レイヤー2: データレジストリ（核心層）(PostgreSQL 15+)        │
│  - 正規化された装備品マスタ                                     │
│  - 調達・契約トランザクション                                   │
│  - 予算・決算レコード                                          │
│  - メーカー・企業レジストリ                                     │
│  - 基地・地域配置情報                                          │
│  - ニュース・報道リンク                                        │
│  - 3Dモデルアセット管理                                        │
│  - 戦略文書引用・文脈データ                                    │
│  - 出典・溯源テーブル                                          │
├─────────────────────────────────────────────────────────────┤
│  レイヤー1: データ収集・抽出パイプライン (Python)               │
│  ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────────────┐ │
│  │ Web Crawler│ │ PDF Parser│ │ OCR Engine│ │ SPECA/docs2formalspec │ │
│  │ (Scrapy)   │ │(pdfplumber│ │ (Tesseract│ │ (NLP Structuring)    │ │
│  └──────────┘ └──────────┘ └──────────┘ └──────────────────┘ │
│  ┌──────────┐ ┌──────────┐                                    │
│  │ Security │ │ Schema   │                                    │
│  │ Filter   │ │ Validator│                                    │
│  │(機密検出) │ │(JSON Sch)│                                    │
│  └──────────┘ └──────────┘                                    │
└─────────────────────────────────────────────────────────────┘
```

---

## 3. データレジストリ設計（核心）

データレジストリは本システムの基盤である。防衛省公開情報の断片的・非構造化性に対し、以下の原則で設計する。

### 3.1 設計原則

1. **正規化と柔軟性のバランス**: 既知のスキーマ（装備品基本属性）を厳密に正規化し、拡張属性は型付きJSON Schemaでバリデーション
2. **一次資料への溯源**: 全レコードに `source_id` を持たせ、出典文書・ページ・URL・ファイルハッシュを追跡
3. **時系列対応**: 全主要エンティティに `valid_from` / `valid_to` を持たせ、歴史を管理（Slowly Changing Dimension Type 2）
4. **外部連携標準**: NATO STANAG、SIPRI、Global Firepower、GS1 GENC（国コード標準）とのマッピングフィールドを確保
5. **機密情報の機械的除外**: 収集パイプラインに機密情報検出フィルタを組み込む

### 3.2 エンティティ一覧（ER図相当）

```
┌──────────────────┐    ┌──────────────────┐    ┌──────────────────┐
│   equipment      │    │   manufacturer   │    │    category      │
│  (装備品マスタ)   │    │   (メーカー)      │    │   (分類体系)      │
├──────────────────┤    ├──────────────────┤    ├──────────────────┤
│ id (PK)          │    │ id (PK)          │    │ id (PK)          │
│ canonical_name   │    │ name             │    │ name             │
│ variant_name     │    │ name_jp          │    │ parent_id (FK)   │
│ model_number     │    │ name_en          │    │ taxonomy_type    │
│ nato_designation │    │ ticker_symbol    │    │ description      │
│ category_id (FK) │◄───┤ country          │    └──────────────────┘
│ service_branch   │    │ is_domestic      │
│ status           │    │ is_prime         │
│ weight_kg        │    │ founded_year     │
│ dimensions       │    │ url              │
│ crew_count       │    │ source_id (FK)   │───► source
│ range_km         │    └──────────────────┘
│ speed_kmh        │
│ unit_cost_yen    │
│ introduced_year  │    ┌──────────────────┐
│ retired_year     │    │   procurement    │
│ total_quantity   │    │   (調達実績)      │
│ image_urls       │    ├──────────────────┤
│ specs_schema_id  │───►│ id (PK)          │
│ specs_json       │    │ equipment_id(FK) │───► equipment
│ manufacturer_id  │───►│ manufacturer_id  │───► manufacturer
│ country_of_origin│    │   (FK)           │
│ is_joint_dev     │    │ contract_number  │
│ joint_partners   │    │ contract_type    │
│ alias_names      │    │ quantity         │
│ source_id (FK)   │───►│ unit_price_yen   │
│ valid_from       │    │ total_amount_yen │
│ valid_to         │    │ currency         │
└──────────────────┘    │ exchange_rate    │
                         │ order_year       │
┌──────────────────┐    │ delivery_start   │
│     source       │    │ delivery_end     │
│   (一次出典)      │    │ delivery_status  │
├──────────────────┤    │ procurement_mthd │
│ id (PK)          │    │ fms_case_id      │
│ source_type      │    │ budget_line_item │
│ title            │    │ competitor_info  │
│ publisher        │    │ notes            │
│ publish_date     │    │ source_id (FK)   │───► source
│ fiscal_year      │    └──────────────────┘
│ url              │
│ file_path        │    ┌──────────────────┐
│ file_hash        │    │    budget        │
│ page_numbers     │    │   (予算レコード)  │
│ section          │    ├──────────────────┤
│ access_date      │    │ id (PK)          │
│ confidence_level │    │ fiscal_year      │
│ notes            │    │ budget_phase     │
└──────────────────┘    │ ministry         │
                        │ budget_category  │
┌──────────────────┐    │ budget_subcat    │
│  equipment_spec  │    │ line_item_name   │
│  _schema         │    │ equipment_id(FK) │───► equipment
│  (型定義テーブル) │    │ amount_requested │
├──────────────────┤    │ amount_approved  │
│ id (PK)          │    │ amount_settled   │
│ category_id (FK) │───►│ quantity_req     │
│ schema_json      │    │ quantity_appr    │
│ version          │    │ source_id (FK)   │───► source
│ description      │    └──────────────────┘
└──────────────────┘

┌──────────────────┐    ┌──────────────────┐    ┌──────────────────┐
│  supply_chain    │    │ equipment_timeline│   │   location     │
│  (部品・供給関係) │    │  (時系列スナップ)  │   │   (基地配置)    │
├──────────────────┤    ├──────────────────┤    ├──────────────────┤
│ id (PK)          │    │ id (PK)          │    │ id (PK)          │
│ parent_equip_id  │───►│ equipment_id(FK) │───►│ equipment_id(FK) │───► equipment
│ child_equip_id   │───►│ fiscal_year      │    │ location_type    │
│ relation_type    │    │ qty_in_service   │    │ name             │
│ quantity_per_unit│    │ qty_ordered      │    │ region           │
│ manufacturer_id  │───►│ qty_retired      │    │ prefecture       │
│ country_of_origin│    │ total_budget_yen│   │ latitude         │
│ is_critical      │    │ status_year_end  │    │ longitude        │
│ source_id (FK)   │───►│ source_id (FK)   │───►│ assigned_unit    │
└──────────────────┘    └──────────────────┘    │ effective_from     │
                                               │ effective_to       │
┌──────────────────┐    ┌──────────────────┐    │ source_id (FK)   │───► source
│   news_article   │    │ equipment_model_3d│   └──────────────────┘
│   (報道・ニュース)│    │   (3Dモデル管理)  │
├──────────────────┤    ├──────────────────┤
│ id (PK)          │    │ id (PK)          │
│ equipment_id(FK) │───►│ equipment_id(FK) │───► equipment
│ title            │    │ model_url        │
│ publisher        │    │ lod_level        │    ┌──────────────────┐
│ published_date   │    │ file_format      │    │strategic_context │
│ url              │    │ file_size_bytes  │    │  (戦略文書引用)   │
│ summary          │    │ bounding_box     │    ├──────────────────┤
│ sentiment        │    │ thumbnail_url    │    │ id (PK)          │
│ source_id (FK)   │───►│ upload_date      │    │ equipment_id(FK) │───► equipment
└──────────────────┘    │ source_id (FK)   │───►│ document_type    │
                        └──────────────────┘    │ quote_text       │
                                               │ context_summary  │
                                               │ strategic_reason │
                                               │ source_id (FK)   │───► source
                                               └──────────────────┘
```

### 3.3 各テーブル詳細定義

#### 3.3.1 `source` — 一次出典マスタ（全データの溯源基盤）

すべての事実はこのテーブルのいずれかの出典に紐づく。同一事実が複数文書で異なる数字を示すことがあるため、矛盾検出の基盤となる。

| カラム | 型 | NOT NULL | 説明 | 例 |
|--------|-----|---------|------|-----|
| `id` | UUID | YES | PK | gen_random_uuid() |
| `source_type` | VARCHAR(50) | YES | 出典種別。Enum: `white_paper`, `budget_request`, `budget_settlement`, `procurement_notice`, `contract_result`, `press_release`, `news_article`, `procurement_site`, `mofa_transfer`, `mod_policy` | `white_paper` |
| `title` | VARCHAR(500) | YES | 文書タイトル | 「防衛白書 2025」 |
| `publisher` | VARCHAR(100) | YES | 発行主体 | `防衛省`, `防衛装備庁`, `外務省` |
| `publish_date` | DATE | NO | 発行日 | 2025-07-12 |
| `fiscal_year` | INTEGER | NO | 対象年度（予算書等）。年度に依存しない文書はNULL | 2026 |
| `url` | TEXT | YES | 公開URL。必ずHTTPSスキーム | `https://www.mod.go.jp/j/publication/wp/...` |
| `file_path` | TEXT | NO | ローカル保存パス | `/data/raw/wp2025.pdf` |
| `file_hash` | VARCHAR(64) | NO | SHA-256。改ざん検知と重複排除 | `e3b0c442...` |
| `page_numbers` | VARCHAR(100) | NO | 該当ページ範囲 | `pp.45-48, p.120` |
| `section` | VARCHAR(200) | NO | 該当章・節タイトル | 「第2部 我が国を取り巻く安全保障環境」 |
| `access_date` | DATE | YES | 最終アクセス日 | 2026-07-22 |
| `confidence_level` | VARCHAR(20) | YES | 一次資料度。Enum: `primary`（一次）, `secondary`（二次解説）, `derived`（推定） | `primary` |
| `notes` | TEXT | NO | 備考・収集時の注意事項 | |
| `created_at` | TIMESTAMP | YES | DEFAULT now() | |

**インデックス**: `source(source_type, fiscal_year)`, `source(publisher, publish_date)`, `source(file_hash)` UNIQUE

**CHECK制約**:
```sql
CONSTRAINT chk_source_url_https CHECK (url ~ '^https://'),
CONSTRAINT chk_source_confidence CHECK (confidence_level IN ('primary', 'secondary', 'derived'))
```

#### 3.3.2 `category` — 装備品分類体系（階層構造）

防衛省の分類とNATO標準（STANAG 2014）、SIPRI分類を両立させる。

| カラム | 型 | NOT NULL | 説明 |
|--------|-----|---------|------|
| `id` | UUID | YES | PK |
| `name` | VARCHAR(100) | YES | 分類名（日本語） |
| `name_en` | VARCHAR(100) | NO | 分類名（英語） |
| `parent_id` | UUID | NO | FK → category.id。自己参照。NULL=ルートカテゴリ |
| `taxonomy_type` | VARCHAR(50) | YES | `mod_standard`, `nato_stanag`, `sipri`, `custom` |
| `description` | TEXT | NO | 説明 |
| `sort_order` | INTEGER | YES | DEFAULT 0。表示順 |
| `source_id` | UUID | YES | FK → source。この分類体系の出典 |

**階層例**（4階層深さまで対応）:
```
ルート: 装備品 (Equipment)
  ├── L1: 航空機 (Aircraft)
  │     ├── L2: 固定翼機 (Fixed-wing)
  │     │     ├── L3: 戦闘機 (Fighter) ← F-35A, F-2
  │     │     ├── L3: 哨戒機 (Patrol)  ← P-1, P-3C
  │     │     └── L3: 輸送機 (Transport) ← C-2, C-130H
  │     ├── L2: 回転翼機 (Rotary-wing)
  │     │     ├── L3: 攻撃ヘリ (Attack) ← AH-64D
  │     │     └── L3: 輸送ヘリ (Transport) ← CH-47J
  │     └── L2: 無人機 (UAV)
  │           └── L3: 偵察型 (ISR) ← Global Hawk
  ├── L1: 艦船 (Naval Vessels)
  │     ├── L2: 護衛艦 (Destroyer/Frigate) ← いずも型, あきづき型
  │     ├── L2: 潜水艦 (Submarine) ← そうりゅう型, たいげい型
  │     └── ...
  ├── L1: 陸上装備 (Ground Equipment)
  └── L1: 誘導武器 (Guided Weapons)
        ├── L2: 空対空 (AAM) ← AIM-120 AMRAAM
        ├── L2: 空対地 (ASM) ← ステルス巡航ミサイル
        └── ...
```

**制約**: `parent_id ≠ id`（循環防止トリガー）

#### 3.3.3 `equipment_spec_schema` — 型付き拡張仕様スキーマ（v2.0新規追加）

`equipment.specs_json` の型安全性を確保するため、カテゴリごとのJSON Schemaを定義し、DBレベルでバリデーションする。

| カラム | 型 | NOT NULL | 説明 |
|--------|-----|---------|------|
| `id` | UUID | YES | PK |
| `category_id` | UUID | YES | FK → category。このスキーマが適用されるカテゴリ |
| `schema_json` | JSONB | YES | JSON Schema（Draft 2020-12準拠） |
| `version` | INTEGER | YES | DEFAULT 1。スキーマバージョン |
| `description` | TEXT | NO | このスキーマの説明 |
| `created_at` | TIMESTAMP | YES | |

**例: 戦闘機カテゴリのスキーマ**:
```json
{
  "type": "object",
  "properties": {
    "max_speed_mach": {"type": "number", "minimum": 0, "maximum": 10},
    "max_speed_kmh": {"type": "integer", "minimum": 0},
    "ceiling_m": {"type": "integer"},
    "thrust_to_weight": {"type": "number"},
    "radar_type": {"type": "string", "enum": ["AESA", "PESA", "Mechanical", "None"]},
    "stealth_level": {"type": "string", "enum": ["VLO", "LO", "Conventional"]},
    "hardpoints": {"type": "integer", "minimum": 0},
    "internal_bay": {"type": "boolean"},
    "engine_count": {"type": "integer", "minimum": 1, "maximum": 8}
  }
}
```

**バリデーション**: `equipment` INSERT/UPDATE時に `category_id` に紐づく `equipment_spec_schema` を参照し、`specs_json` が `schema_json` に準拠するかをトリガーまたはアプリ層で検証。

#### 3.3.4 `equipment` — 装備品マスタ（システム中核）

1装備品1レコード。バリアント（Block 4等）は `variant_name` で区別し、別レコードにはしない。

| カラム | 型 | NOT NULL | 説明 | 例 |
|--------|-----|---------|------|-----|
| `id` | UUID | YES | PK | |
| `canonical_name` | VARCHAR(200) | YES | 正式名称（日本語） | 「F-35A ライトニングII」 |
| `variant_name` | VARCHAR(200) | NO | バリアント名 | 「F-35A Block 4」 |
| `model_number` | VARCHAR(100) | NO | 型式番号 | 「F-35A」 |
| `nato_designation` | VARCHAR(50) | NO | NATO報告名称 | 「Lightning II」 |
| `category_id` | UUID | YES | FK → category | |
| `service_branch` | VARCHAR(50) | YES | 自衛隊種別。Enum: `航空自衛隊`, `海上自衛隊`, `陸上自衛隊` | |
| `status` | VARCHAR(50) | YES | Enum: `active`, `planned`, `retired`, `prototype`, `cancelled`, `under_development` | `active` |
| `weight_kg` | DECIMAL(12,2) | NO | 重量(kg)。NULL許容 | 13154.00 |
| `dimensions` | JSONB | NO | 全長×全幅×全高(m) | `{"length_m": 15.7, "width_m": 10.7, "height_m": 4.4}` |
| `crew_count` | INTEGER | NO | 乗員数 | 1 |
| `range_km` | INTEGER | NO | 航続距離/射程(km) | 2200 |
| `speed_kmh` | INTEGER | NO | 最高速度(km/h) | 1930 |
| `unit_cost_yen` | BIGINT | NO | 最新の契約単価(円)。NULL許容 | 14300000000 |
| `total_cost_yen` | BIGINT | NO | プログラム総額(円)。開発費含む場合あり | 1500000000000 |
| `introduced_year` | INTEGER | NO | 自衛隊導入開始年 | 2019 |
| `retired_year` | INTEGER | NO | 退役予定/完了年。NULL=未退役 | NULL |
| `total_quantity` | INTEGER | NO | 保有/導入予定総数（最新値） | 147 |
| `manufacturer_id` | UUID | NO | FK → manufacturer。主契約者 | |
| `country_of_origin` | VARCHAR(50) | NO | 開発国。ISO 3166-1 alpha-3準拠 | `USA` |
| `is_joint_dev` | BOOLEAN | YES | DEFAULT FALSE。国際共同開発 | TRUE |
| `joint_partners` | JSONB | NO | 共同開発国リスト（ISOコード） | `["USA", "GBR", "ITA", "NLD", "AUS", "CAN", "TUR", "DNK", "NOR"]` |
| `image_urls` | JSONB | NO | 画像URLリスト | `[{"url": "https://...", "caption": "F-35A 飛行", "source": "防衛省"}]` |
| `specs_schema_id` | UUID | NO | FK → equipment_spec_schema。NULL=未分類 | |
| `specs_json` | JSONB | NO | 拡張仕様。`equipment_spec_schema` で型定義 | `{"max_speed_mach": 1.6, "radar_type": "AESA", "stealth_level": "VLO"}` |
| `alias_names` | JSONB | NO | 別名リスト（省略形等） | `["35戦闘機", "Lightning II", "ADSF"]` |
| `source_id` | UUID | YES | FK → source | |
| `created_at` | TIMESTAMP | YES | DEFAULT now() | |
| `updated_at` | TIMESTAMP | YES | DEFAULT now() | |
| `valid_from` | DATE | YES | DEFAULT '1900-01-01' | |
| `valid_to` | DATE | NO | NULL=現在有効 | |

**インデックス**: `equipment(category_id)`, `equipment(service_branch)`, `equipment(status)`, `equipment(introduced_year)`, `equipment(manufacturer_id)`, `equipment USING gin (canonical_name gin_trgm_ops)`, `equipment USING gin (alias_names)`

**UNIQUE制約**: `(canonical_name, variant_name, valid_from)` — 同一名称・バリアントで時系列重複防止

**CHECK制約**:
```sql
CONSTRAINT chk_equipment_introduced_retired CHECK (retired_year IS NULL OR introduced_year <= retired_year),
CONSTRAINT chk_equipment_status CHECK (status IN ('active', 'planned', 'retired', 'prototype', 'cancelled', 'under_development'))
```

#### 3.3.5 `manufacturer` — メーカー/企業レジストリ

| カラム | 型 | NOT NULL | 説明 |
|--------|-----|---------|------|
| `id` | UUID | YES | PK |
| `name` | VARCHAR(200) | YES | 企業名（英語） |
| `name_jp` | VARCHAR(200) | NO | 企業名（日本語） |
| `ticker_symbol` | VARCHAR(20) | NO | 証券コード（東証等） |
| `country` | VARCHAR(50) | YES | 本社国。ISO 3166-1 alpha-3準拠 |
| `is_domestic` | BOOLEAN | YES | DEFAULT FALSE。国内企業フラグ |
| `is_prime_contractor` | BOOLEAN | YES | DEFAULT FALSE。主契約者フラグ |
| `founded_year` | INTEGER | NO | 設立年 |
| `employees_count` | INTEGER | NO | 従業員数（概算） |
| `defense_revenue_yen` | BIGINT | NO | 直近年度の防衛関連売上（円） |
| `url` | TEXT | NO | 企業公式URL |
| `parent_company_id` | UUID | NO | FK → manufacturer。親子関係 |
| `source_id` | UUID | YES | FK → source |
| `created_at` | TIMESTAMP | YES | |

**インデックス**: `manufacturer USING gin (name_jp gin_trgm_ops)`, `manufacturer(country)`, `manufacturer(is_domestic)`

#### 3.3.6 `procurement` — 調達・契約トランザクション

個別の調達契約を記録。時系列分析と予算フロー可視化の基盤。同一装備品が複数年にわたって調達されるため、年度ごとにレコードを分ける。

| カラム | 型 | NOT NULL | 説明 | 例 |
|--------|-----|---------|------|-----|
| `id` | UUID | YES | PK | |
| `equipment_id` | UUID | YES | FK → equipment | |
| `manufacturer_id` | UUID | NO | FK → manufacturer。複数の場合は主契約者 | |
| `contract_number` | VARCHAR(100) | NO | 契約番号（公表されている場合） | |
| `contract_type` | VARCHAR(50) | YES | `open_competition`, `selective`, `negotiated`, `sole_source` | `negotiated` |
| `quantity` | INTEGER | YES | 調達数量 | 8 |
| `unit_price_yen` | BIGINT | NO | 単価（円） | 14300000000 |
| `total_amount_yen` | BIGINT | YES | 契約総額（円） | 114400000000 |
| `currency` | VARCHAR(3) | YES | DEFAULT 'JPY' | `JPY`, `USD` |
| `exchange_rate` | DECIMAL(10,4) | NO | 為替レート（外貨建の場合）。財務省の公開データで補完 | 145.32 |
| `order_year` | INTEGER | YES | 発注年度（年度） | 2025 |
| `delivery_start_year` | INTEGER | NO | 納入開始年度 | 2026 |
| `delivery_end_year` | INTEGER | NO | 納入完了予定年度 | 2028 |
| `delivery_status` | VARCHAR(50) | YES | `pending`, `in_progress`, `completed`, `delayed`, `cancelled`, `partial` | `in_progress` |
| `procurement_method` | VARCHAR(100) | NO | `FMS_GSA`（無償資金）, `FMS_FMS`（有償資金）, `domestic`, `international_joint`, `commercial` | `FMS_FMS` |
| `fms_case_id` | VARCHAR(100) | NO | FMSケース番号 | `JA-12345` |
| `budget_line_item` | VARCHAR(200) | NO | 予算科目名 | 「戦闘機（F-35A）」 |
| `competitor_info` | JSONB | NO | 競合参加企業情報 | `[{"name": "案B: B社", "result": "non_selected"}]` |
| `notes` | TEXT | NO | 備考・特殊条件 | |
| `source_id` | UUID | YES | FK → source | |
| `created_at` | TIMESTAMP | YES | | |

**インデックス**: `procurement(equipment_id)`, `procurement(order_year)`, `procurement(manufacturer_id)`, `procurement(delivery_status)`

**CHECK制約**:
```sql
CONSTRAINT chk_procurement_amount CHECK (
  total_amount_yen BETWEEN (unit_price_yen * quantity * 0.95) AND (unit_price_yen * quantity * 1.05)
  OR unit_price_yen IS NULL  -- 一括契約で単価不明の場合
),
CONSTRAINT chk_procurement_delivery_year CHECK (delivery_end_year IS NULL OR delivery_start_year <= delivery_end_year),
CONSTRAINT chk_procurement_currency CHECK (currency IN ('JPY', 'USD', 'EUR', 'GBP'))
```

#### 3.3.7 `budget` — 予算・決算レコード

| カラム | 型 | NOT NULL | 説明 |
|--------|-----|---------|------|
| `id` | UUID | YES | PK |
| `fiscal_year` | INTEGER | YES | 年度 |
| `budget_phase` | VARCHAR(50) | YES | `request`（概算要求）, `approved`（国会承認）, `settlement`（決算） |
| `ministry` | VARCHAR(50) | YES | DEFAULT '防衛省' |
| `budget_category` | VARCHAR(100) | YES | 大分類 |
| `budget_subcategory` | VARCHAR(100) | NO | 中分類 |
| `line_item_name` | VARCHAR(200) | YES | 明細名 |
| `line_item_code` | VARCHAR(50) | NO | 予算科目コード（公表されている場合） |
| `equipment_id` | UUID | NO | FK → equipment。紐付けできない場合はNULL |
| `amount_requested_yen` | BIGINT | NO | 要求額 |
| `amount_approved_yen` | BIGINT | NO | 承認額 |
| `amount_settled_yen` | BIGINT | NO | 決算額 |
| `quantity_requested` | INTEGER | NO | 要求数量 |
| `quantity_approved` | INTEGER | NO | 承認数量 |
| `source_id` | UUID | YES | FK → source |

**インデックス**: `budget(fiscal_year)`, `budget(budget_phase)`, `budget(equipment_id)`, `budget(line_item_code)`

#### 3.3.8 `supply_chain` — 部品・供給関係

装備品の部品構成（F-35A → F135エンジン）と企業間の供給ネットワーク。

| カラム | 型 | NOT NULL | 説明 |
|--------|-----|---------|------|
| `id` | UUID | YES | PK |
| `parent_equipment_id` | UUID | YES | FK → equipment。親システム |
| `child_equipment_id` | UUID | YES | FK → equipment。子部品/サブシステム |
| `relation_type` | VARCHAR(50) | YES | `engine`, `avionics`, `radar`, `weapon`, `sensor`, `communication`, `propulsion`, `landing_gear`, `fuel_system`, `electrical`, `structural`, `software` |
| `quantity_per_unit` | INTEGER | YES | DEFAULT 1。1基あたりの搭載数 |
| `manufacturer_id` | UUID | NO | FK → manufacturer。部品メーカー |
| `country_of_origin` | VARCHAR(50) | NO | 部品の開発国（ISO 3166-1 alpha-3） |
| `is_critical` | BOOLEAN | YES | DEFAULT FALSE。重要部品フラグ |
| `is_export_controlled` | BOOLEAN | YES | DEFAULT FALSE。輸出管理対象品目 |
| `notes` | TEXT | NO | |
| `source_id` | UUID | YES | FK → source |

**CHECK制約**: `parent_equipment_id ≠ child_equipment_id`（自己参照防止）

**インデックス**: `supply_chain(parent_equipment_id)`, `supply_chain(child_equipment_id)`

#### 3.3.9 `equipment_timeline` — 装備品時系列スナップショット

年度ごとの保有数・予算・ステータスの歴史。`equipment.total_quantity` の最新値を補完する時系列データ。

| カラム | 型 | NOT NULL | 説明 |
|--------|-----|---------|------|
| `id` | UUID | YES | PK |
| `equipment_id` | UUID | YES | FK → equipment |
| `fiscal_year` | INTEGER | YES | 年度 |
| `quantity_in_service` | INTEGER | NO | 当年度末の現役保有数 |
| `quantity_ordered` | INTEGER | NO | 当年度の新規調達発注数 |
| `quantity_delivered` | INTEGER | NO | 当年度の納入数 |
| `quantity_retired` | INTEGER | NO | 当年度の退役数 |
| `total_budget_yen` | BIGINT | NO | 当年度の該当予算額 |
| `cumulative_quantity` | INTEGER | NO | 当年度末の累積導入数（導入開始から） |
| `status_at_year_end` | VARCHAR(50) | NO | `active`, `delivering`, `phase_out`, `retired`, `not_yet` |
| `source_id` | UUID | YES | FK → source |

**UNIQUE制約**: `(equipment_id, fiscal_year)` — 同一装備品・同一年度の重複防止

**インデックス**: `equipment_timeline(equipment_id, fiscal_year)`

#### 3.3.10 `location` — 基地・地域配置情報（v2.0新規追加）

装備品がどの基地に配備されているかを管理。issue要件の「いつ・どこで」を満たす。

| カラム | 型 | NOT NULL | 説明 | 例 |
|--------|-----|---------|------|-----|
| `id` | UUID | YES | PK | |
| `equipment_id` | UUID | YES | FK → equipment | |
| `location_type` | VARCHAR(50) | YES | `base`（基地）, `depot`（整備場）, `training`（訓練場）, `ship_home_port`（艦船母港） | `base` |
| `name` | VARCHAR(200) | YES | 場所名称 | 「三沢基地」 |
| `region` | VARCHAR(50) | NO | 地方 | 「東北」 |
| `prefecture` | VARCHAR(50) | NO | 都道府県 | 「青森県」 |
| `city` | VARCHAR(100) | NO | 市区町村 | 「三沢市」 |
| `latitude` | DECIMAL(10,8) | NO | 緯度（WGS84） | 40.70000000 |
| `longitude` | DECIMAL(11,8) | NO | 経度（WGS84） | 141.36666667 |
| `assigned_unit` | VARCHAR(200) | NO | 配備部隊名 | 「航空自衛隊 第3航空団」 |
| `quantity_at_location` | INTEGER | NO | 配備数 | 26 |
| `effective_from` | DATE | YES | 配備開始日 | 2019-01-01 |
| `effective_to` | DATE | NO | 配備終了日（移動/退役時） | NULL |
| `source_id` | UUID | YES | FK → source |

**インデックス**: `location(equipment_id)`, `location(name)`, `location USING gist (point(longitude, latitude))`（PostGIS拡張）

#### 3.3.11 `news_article` — 報道・ニュースリンク（v2.0新規追加）

issue要件の「関連ニュース」を構造化して管理。

| カラム | 型 | NOT NULL | 説明 |
|--------|-----|---------|------|
| `id` | UUID | YES | PK |
| `equipment_id` | UUID | YES | FK → equipment |
| `title` | VARCHAR(500) | YES | 記事タイトル |
| `publisher` | VARCHAR(200) | YES | 発行メディア |
| `published_date` | DATE | YES | 公開日 |
| `url` | TEXT | YES | 記事URL |
| `summary` | TEXT | NO | 要約（自動/手動） |
| `sentiment` | VARCHAR(20) | NO | `positive`, `neutral`, `negative`, `controversial`（自動分析） |
| `keywords` | JSONB | NO | 抽出キーワード |
| `source_id` | UUID | YES | FK → source |

**インデックス**: `news_article(equipment_id)`, `news_article(published_date)`

#### 3.3.12 `equipment_model_3d` — 3Dモデルアセット管理（v2.0新規追加）

Three.jsで使用する3Dモデルのバージョン管理とLOD制御。

| カラム | 型 | NOT NULL | 説明 | 例 |
|--------|-----|---------|------|-----|
| `id` | UUID | YES | PK | |
| `equipment_id` | UUID | YES | FK → equipment | |
| `model_url` | TEXT | YES | glTF/GLBファイルのURL | `/models/f35a_lod0.glb` |
| `lod_level` | INTEGER | YES | 詳細度レベル。0=最高、3=最低 | 0 |
| `file_format` | VARCHAR(20) | YES | `glb`, `gltf`, `obj`, `fbx` | `glb` |
| `file_size_bytes` | INTEGER | YES | ファイルサイズ | 2457600 |
| `vertex_count` | INTEGER | NO | 頂点数 | 15000 |
| `face_count` | INTEGER | NO | 面数 | 8000 |
| `bounding_box` | JSONB | NO | バウンディングボックス | `{"width": 10.7, "height": 4.4, "depth": 15.7}` |
| `thumbnail_url` | TEXT | NO | プレビュー画像 | `/thumbnails/f35a.png` |
| `license` | VARCHAR(50) | YES | `cc_by_4`, `mod_gov`, `proprietary`, `unknown` | `mod_gov` |
| `is_generated` | BOOLEAN | YES | DEFAULT FALSE。AI生成モデルか | FALSE |
| `upload_date` | DATE | YES | | |
| `source_id` | UUID | YES | FK → source |

**インデックス**: `equipment_model_3d(equipment_id, lod_level)`

#### 3.3.13 `strategic_context` — 戦略文書引用・文脈データ（v2.0新規追加）

防衛大綱・中期防衛・国家防衛戦略からの「なぜこの装備が必要か」の文脈を保存。

| カラム | 型 | NOT NULL | 説明 |
|--------|-----|---------|------|
| `id` | UUID | YES | PK |
| `equipment_id` | UUID | YES | FK → equipment |
| `document_type` | VARCHAR(50) | YES | `defense_program_guidelines`, `mid_term_defense`, `national_defense_strategy`, `budget_request_explanation` |
| `quote_text` | TEXT | YES | 原文引用 |
| `context_summary` | TEXT | NO | 文脈要約 |
| `strategic_reason` | TEXT | NO | 「なぜこの装備が必要か」の要約 |
| `threat_assessment` | TEXT | NO | 対象とする脅威の要約 |
| `capability_gap` | TEXT | NO | 能力差の説明 |
| `source_id` | UUID | YES | FK → source |

**インデックス**: `strategic_context(equipment_id)`, `strategic_context(document_type)`

### 3.4 インデックス設計（性能と検索性）

```sql
-- 検索・フィルタ性能
CREATE INDEX idx_equipment_category ON equipment(category_id);
CREATE INDEX idx_equipment_service ON equipment(service_branch);
CREATE INDEX idx_equipment_status ON equipment(status);
CREATE INDEX idx_equipment_introduced ON equipment(introduced_year);
CREATE INDEX idx_equipment_manufacturer ON equipment(manufacturer_id);
CREATE INDEX idx_equipment_country ON equipment(country_of_origin);

-- 調達データ
CREATE INDEX idx_procurement_equipment ON procurement(equipment_id);
CREATE INDEX idx_procurement_year ON procurement(order_year);
CREATE INDEX idx_procurement_manufacturer ON procurement(manufacturer_id);
CREATE INDEX idx_procurement_status ON procurement(delivery_status);
CREATE INDEX idx_procurement_fms ON procurement(fms_case_id) WHERE fms_case_id IS NOT NULL;

-- 予算データ
CREATE INDEX idx_budget_fiscal ON budget(fiscal_year);
CREATE INDEX idx_budget_phase ON budget(fiscal_year, budget_phase);
CREATE INDEX idx_budget_equipment ON budget(equipment_id);
CREATE INDEX idx_budget_line_item ON budget(line_item_name);

-- 時系列データ
CREATE INDEX idx_timeline_equipment_year ON equipment_timeline(equipment_id, fiscal_year);
CREATE INDEX idx_timeline_year ON equipment_timeline(fiscal_year);

-- サプライチェーン
CREATE INDEX idx_supply_chain_parent ON supply_chain(parent_equipment_id);
CREATE INDEX idx_supply_chain_child ON supply_chain(child_equipment_id);
CREATE INDEX idx_supply_chain_critical ON supply_chain(is_critical) WHERE is_critical = TRUE;

-- 基地配置（PostGIS使用時）
-- CREATE INDEX idx_location_geo ON location USING gist (ll_to_earth(latitude, longitude));

-- 出典
CREATE INDEX idx_source_type ON source(source_type, fiscal_year);
CREATE INDEX idx_source_publisher ON source(publisher, publish_date);

-- 全文検索（pg_trgm拡張必須）
CREATE INDEX idx_equipment_name_trgm ON equipment USING gin (canonical_name gin_trgm_ops);
CREATE INDEX idx_equipment_alias_trgm ON equipment USING gin (alias_names gin_trgm_ops);
CREATE INDEX idx_manufacturer_name_trgm ON manufacturer USING gin (name_jp gin_trgm_ops);
CREATE INDEX idx_manufacturer_name_en_trgm ON manufacturer USING gin (name gin_trgm_ops);
CREATE INDEX idx_news_title_trgm ON news_article USING gin (title gin_trgm_ops);
```

### 3.5 データ品質ルール（DB制約 + アプリ層 + 監視）

| ルール | 実装場所 | 内容 | 違反時の処理 |
|--------|---------|------|-------------|
| **溯源必須** | DB制約 | `source_id IS NOT NULL`（全テーブル） | INSERT拒否 |
| **金額整合** | DB制約（緩和） | `procurement.total_amount_yen` ≈ `quantity × unit_price_yen`（許容誤差±5%） | 警告ログ出力、INSERT許可（手動レビューフラグ付き） |
| **年度整合** | DB制約 | `introduced_year ≤ retired_year` | INSERT拒否 |
| **階層循環防止** | DBトリガー | `category.parent_id ≠ category.id`、さらに祖先循環も検出 | INSERT/UPDATE拒否 |
| **重複防止** | UNIQUE | `(canonical_name, variant_name, valid_from)` | INSERT拒否 |
| **NULL戦略** | DB制約 | 数値カラムはNULL許容（データ欠損を明示）、テキスト必須カラムはNOT NULL | INSERT拒否 |
| **スキーマ準拠** | DBトリガー + アプリ層 | `equipment.specs_json` が `equipment_spec_schema.schema_json` に準拠 | INSERT/UPDATE拒否 |
| **HTTPS出典** | DB制約 | `source.url` は `^https://` で始まる | INSERT拒否 |
| **出典整合** | アプリ層 | `budget.amount_approved_yen` ≥ `budget.amount_requested_yen` の原則（減額の例外あり） | 警告フラグ付きINSERT |
| **地理整合** | アプリ層 | `location.latitude` が -90〜90、`longitude` が -180〜180 | INSERT拒否 |
| **時系列連続** | アプリ層 | `equipment_timeline` の同一装備品で年度が飛んでいないかチェック | 欠損年度を自動検出 |

### 3.6 具体例: F-35A のデータフロー（v2.0新規追加）

```
[source] id=s1
  title="防衛白書 2025"
  publisher="防衛省"
  url="https://www.mod.go.jp/j/publication/wp/wp2025.pdf"
  page_numbers="pp.258-259"
  confidence_level="primary"

  ↓

[category] id=c1
  name="戦闘機"
  parent_id=「固定翼機」
  taxonomy_type="mod_standard"

  ↓

[equipment_spec_schema] id=ss1
  category_id=c1
  schema_json={戦闘機固有の性能パラメータ定義}

  ↓

[equipment] id=e1
  canonical_name="F-35A ライトニングII"
  variant_name=NULL（標準型）
  model_number="F-35A"
  nato_designation="Lightning II"
  category_id=c1
  service_branch="航空自衛隊"
  status="active"
  introduced_year=2019
  retired_year=NULL
  total_quantity=147（計画）
  country_of_origin="USA"
  is_joint_dev=TRUE
  joint_partners=["USA", "GBR", "ITA", "NLD", "AUS", "CAN", "TUR", "DNK", "NOR"]
  specs_schema_id=ss1
  specs_json={"max_speed_mach": 1.6, "radar_type": "AESA", "stealth_level": "VLO", "internal_bay": true}
  alias_names=["35戦闘機", "ADSF"]
  source_id=s1

  ↓ 複数レコード

[procurement] id=p1
  equipment_id=e1
  order_year=2011
  quantity=4
  unit_price_yen=10200000000
  total_amount_yen=40800000000
  procurement_method="FMS_FMS"
  fms_case_id="JA-P-BIH"
  source_id=s2（別source: FY2012予算書）

[procurement] id=p2
  equipment_id=e1
  order_year=2020
  quantity=105
  unit_price_yen=14300000000
  total_amount_yen=150150000000
  procurement_method="FMS_FMS"
  source_id=s3（別source: FY2021予算書）

  ↓

[budget] id=b1
  fiscal_year=2025
  budget_phase="approved"
  line_item_name="戦闘機（F-35A）"
  equipment_id=e1
  amount_approved_yen=154900000000
  quantity_approved=8
  source_id=s4（FY2025予算書）

  ↓ 時系列

[equipment_timeline] id=t1
  equipment_id=e1
  fiscal_year=2019
  quantity_in_service=0
  quantity_ordered=4
  status_at_year_end="delivering"

[equipment_timeline] id=t2
  equipment_id=e1
  fiscal_year=2020
  quantity_in_service=2
  quantity_delivered=2
  status_at_year_end="active"

  ↓

[location] id=l1
  equipment_id=e1
  location_type="base"
  name="三沢基地"
  prefecture="青森県"
  latitude=40.70000000
  longitude=141.36666667
  assigned_unit="航空自衛隊 第3航空団"
  quantity_at_location=26
  effective_from="2018-01-01"

  ↓

[supply_chain] id=sc1
  parent_equipment_id=e1
  child_equipment_id=e2（F135エンジン）
  relation_type="engine"
  quantity_per_unit=1
  manufacturer_id=m1（Pratt & Whitney）
  is_critical=TRUE

  ↓

[news_article] id=n1
  equipment_id=e1
  title="航空自衛隊 F-35Aが緊急着陸"
  publisher="NHK"
  published_date="2025-03-15"
  url="https://www3.nhk.or.jp/..."

  ↓

[strategic_context] id=st1
  equipment_id=e1
  document_type="national_defense_strategy"
  quote_text="...我が国周辺における航空優勢を確保するため..."
  strategic_reason="中国・ロシアの第5世代戦闘機に対する対抗能力"
```

---

## 4. データ収集パイプライン設計

### 4.1 収集対象ソースと構造

| ソース | URL | フォーマット | 収集頻度 | 主なデータ | 難易度 |
|--------|-----|-------------|---------|-----------|--------|
| 防衛省 予算概算要求 | https://www.mod.go.jp/j/budget/ | PDF | 年度1回（8月頃） | 予算額、数量、装備品名 | 中（表構造が変わる） |
| 防衛省 歳出決算 | https://www.mod.go.jp/j/budget/ | PDF | 年度1回 | 決算額、執行率 | 中 |
| 防衛白書 | https://www.mod.go.jp/j/publication/wp/ | PDF | 年度1回（7月頃） | 保有装備数、部隊編成、戦略文脈 | 高（表が画像の場合あり） |
| 防衛装備庁 調達情報 | https://www.mod.go.jp/atla/ | HTML/PDF | 継続（随時） | 契約情報、入札結果 | 低 |
| 防衛省 入札情報 | https://www.mod.go.jp/j/procurement/ | HTML | 継続 | 落札結果、金額 | 中（Cloudflare保護） |
| 中期防衛力整備計画 | https://www.mod.go.jp/j/policy/ | PDF | 5年ごと | 5年計画の装備整備方針 | 中 |
| 国家防衛戦略 | https://www.mod.go.jp/j/policy/ | PDF | 更新時 | 戦略優先度 | 低 |
| 防衛大綱 | https://www.mod.go.jp/j/policy/ | PDF | 10年ごと | 基本的防衛力構想 | 低 |
| 外務省 防衛装備移転 | https://www.mofa.go.jp/mofaj/gaiko/ | HTML/PDF | 随時 | 輸出入情報 | 低 |

### 4.2 パイプラインステージ（v2.0改訂：セキュリティフィルタ追加）

```
Stage 1: Fetch          →  wget/curl でPDF/HTMLを取得。robots.txt 遵守。
         └─→ robots.txt 確認 → User-agent: DefenseEquipmentBot / Crawl-delay: 5

Stage 2: Extract        →  pdfplumber / BeautifulSoup でテキスト・表抽出
         └─→ 表が画像の場合は OCR フォールバック

Stage 3: OCR            →  スキャンPDFは Tesseract (jpn+jpn_vert) でテキスト化
         └─→ DPI 300以上で処理

Stage 4: Security Filter→  機密情報検出（v2.0追加）
         ├─→ 文書分類: 公開文書かの自動判定（機密マーク検出）
         ├─→ キーワードフィルタ: 「機密」「秘密」「極秘」等のマーク検出
         ├─→ 画像解析: 黒塗り部分の検出
         └─→ NGリスト: 非公開URLパターンのブロック
         └─→ 判定結果: PASS → Stage 5 / REJECT → ログ記録 + 破棄

Stage 5: Structure      →  SPECA/docs2formalspec NLP パイプラインで構造化
         └─→ エンティティ抽出（装備品名、金額、数量）
         └─→ 関係抽出（装備品→予算、装備品→メーカー）

Stage 6: Schema Validate→  equipment.specs_json のスキーマバリデーション（v2.0追加）
         └─→ equipment_spec_schema に準拠しているか検証

Stage 7: Quality Gate   →  データ品質チェック
         ├─→ 金額整合（±5%許容）
         ├─→ 年度整合
         ├─→ 重複チェック
         └─→ 結果: PASS / WARN（手動レビュー） / FAIL（拒否）

Stage 8: Load           →  DBにUPSERT（既存レコードの更新）
         └─→ ON CONFLICT (unique_key) DO UPDATE

Stage 9: Provenance     →  sourceテーブルに出典を登録
         └─→ file_hash計算、重複排除
```

### 4.3 セキュリティガードレール詳細（v2.0新規追加）

公開情報のみを扱うという制約を機械的に保証するための設計。

| ガードレール | 実装 | 詳細 |
|-------------|------|------|
| **ドメインホワイトリスト** | Fetch前 | `*.mod.go.jp`, `*.mofa.go.jp`, `*.go.jp` のみ許可。それ以外は拒否 |
| **URLパターンブラックリスト** | Fetch前 | 非公開文書のパスパターンをブロック（例: `/internal/`, `/confidential/`） |
| **機密マーク検出** | Extract後 | 「機密」「秘密」「極秘」「CONFIDENTIAL」「SECRET」「TOP SECRET」の文字列検出。ヒットした文書は全パイプラインを停止 |
| **黒塗り検出** | OCR後 | 画像内の黒塗り領域の面積比率を計算。閾値（例: 5%）超過で警告 |
| **文書分類モデル** | Extract後 | 公開文書 vs 内部文書を分類する軽量MLモデル（公開文書の特徴を学習） |
| **人間レビュー** | Load前 | 新規source_typeや初回の未知ドメインからの収集は必ず手動確認 |
| **ログ監査** | 全ステージ | 全処理を監査ログに記録。後から誰がいつどの文書を処理したか追跡可能 |

### 4.4 構造化の課題と対策

| 課題 | 対策 | 優先度 |
|------|------|--------|
| PDF中の表が画像として埋め込まれている | pdfplumberの `extract_table()` + OCRフォールバック。DPI 300以上で再スキャン | P0 |
| 装備品名が省略形（例: 「35戦闘機」） | `equipment.alias_names`（JSONB）で別名管理 + trigram全文検索 | P0 |
| 金額が「億円」「百万円」表記 | 正規表現 `([0-9,]+)\s*([億万]円)` で抽出し、円換算 | P0 |
| 同一装備品が複数文書で異なる名称 | `equipment.alias_names` で別名管理。名称変更履歴は `valid_from`/`valid_to` で管理 | P0 |
| 予算書の「項」が装備品と必ずしも1:1でない | `budget.equipment_id` はNULL許容。紐付けできない場合は `line_item_name` のみ記録し、`budget.equipment_id` は後から手動レビュー | P1 |
| FMS調達の外貨建契約 | `currency` + `exchange_rate` カラム。為替レートは財務省の公開データ（https://www.mof.go.jp/）で補完 | P1 |
| 中期防衛計画の「能力目標」が抽象的 | `strategic_context` テーブルに「能力目標→具体的装備」の推論を記録。確度フラグ（`confirmed`/`inferred`/`speculative`）を付与 | P2 |
| 複数年度にわたる一括契約の年度配分 | `procurement` レコードの `order_year` は「決済年度」ではなく「公表年度」とし、複数年度にわたる契約は各年度の予算書から個別に抽出 | P1 |

---

## 5. 3D可視化層設計

### 5.1 3Dマッピングの座標体系

| 軸 | 割当て | 値域 | スケール | 例 |
|----|--------|------|---------|-----|
| **X** | 調達年度 | 2000〜2040 | 線形（1年=1単位） | 左から右へ時系列 |
| **Y** | 予算規模 | 10億〜10兆円 | 対数（log10） | 下から上へ規模拡大 |
| **Z** | 装備品カテゴリ | 4大カテゴリ | カテゴリ間隔=固定 | 奥から手前へ分類 |

**設計意図**: X軸=時間で導入時期の流れを表現。Y軸=予算規模で経済的インパクトを視覚化。Z軸=カテゴリで空間的分離を実現。これにより「いつ・どれだけ・何の装備」が一目で把握できる。

### 5.2 ノード（装備品）の視覚属性

| 属性 | エンコーディング | 値 | 備考 |
|------|----------------|-----|------|
| **形状** | カテゴリ別 | 戦闘機=△、艦船=□、車両=○、誘導弾=♦、ヘリ=⬡ | `equipment_model_3d` が存在する場合は3Dモデルに置き換え |
| **色** | メーカー/国別 | 三菱重工=赤(#E74C3C)、川崎重工=青(#3498DB)、IHI=緑(#2ECC71)、海外=灰色系 | `manufacturer.country` でデフォルト色決定 |
| **サイズ** | 単価の対数 | `node_size = 0.5 + log10(unit_cost_yen / 1e9) * 0.3` | 10億円=0.8、100億円=1.1、1兆円=1.4 |
| **透明度** | 運用状況 | active=1.0、planned=0.6、under_development=0.5、retired=0.2、cancelled=0.1 | |
| **輪郭** | 国産/海外 | 国産=実線(2px)、海外=破線(2px, dash=[5,3]) | `equipment.is_joint_dev` で実線+点線の複合 |
| **エミッション** | 最新調達 | 直近3年の調達品が `emissiveIntensity = 0.3` で光る | 年度スライダーと連動 |
| **アニメーション** | 状態変化 | 新規導入時: scale 0→1（0.5秒 ease-out）、退役時: opacity 1→0（0.3秒） | |

### 5.3 LOD（詳細度）制御（v2.0新規追加）

| LODレベル | トリガー条件 | 装備品表示 | 備考 |
|-----------|-----------|-----------|------|
| **LOD 0** | カメラ距離 < 50 | glTF 3Dモデル（`equipment_model_3d`） | 最詳細。回転・ズーム可能 |
| **LOD 1** | 50 ≤ 距離 < 150 | 高解像度アイコン（SVG, 64×64px） | 形状識別可能 |
| **LOD 2** | 150 ≤ 距離 < 400 | 低解像度アイコン（SVG, 32×32px） | カテゴリ識別のみ |
| **LOD 3** | 400 ≤ 距離 | 点（Point, 4px） | 分布のみ。ラベル非表示 |

**パフォーマンス基準**:
- 目標FPS: 60fps（デスクトップ）、30fps（モバイル）
- 同時表示ノード上限: LOD 0=50個、LOD 1=200個、LOD 2=1000個、LOD 3=無制限
- インスタンシング: 同一カテゴリ・同一LODのノードはInstancedMeshで描画

### 5.4 エッジ（関係）の視覚属性

| 関係タイプ | エッジ表現 | 色 | アニメーション |
|-----------|-----------|-----|--------------|
| 部品→親装備（`supply_chain`） | 細線(1px)+矢印 | #7F8C8D（グレー） | パーティクル流（点が線を流れる） |
| メーカー→装備品（`procurement`） | 点線(1px, dash=[3,3]) | メーカー色 | なし |
| 予算→装備品（`budget`） | 太線(2px)+グラデーション | 金額に応じた濃淡（薄黄→濃橙） | なし |
| 代替関係 | 波線(1.5px) | #E67E22（オレンジ） | 点滅（1Hz） |
| 基地配置（`location`） | 点線(0.5px)+小円 | #3498DB（青） | なし |

### 5.5 時系列アニメーションの仕様

1. **年度スライダー**: 2000〜2035年をスライダーで指定（1年刻み）
2. **プレイボタン**: 自動再生（1年/1.5秒）。再生中は操作をロックしない
3. **表示ロジック**:
   - `introduced_year ≤ スライダー年度` の装備品をフェードイン（opacity 0→1, 0.3秒）
   - `retired_year ≤ スライダー年度` の装備品をフェードアウト（opacity 1→0.2, 0.3秒）
   - `status = planned AND 導入予定年度 > スライダー年度` は非表示
   - 年度スライダー変更時、カメラが自動でその年度のノード群にフォーカス（オプション）
4. **累積情報HUD表示**:
   - スライダー年度までの累積調達額
   - 現役保有総数（航空機/艦船/陸上/誘導武器 別）
   - 当年度の新規導入リスト（最大5件）

### 5.6 メーカー・サプライチェーンマップ

別ビューとして提供。Force-directed graph（D3.js or Three.js Sprite）:
- **ノード**: 企業（`manufacturer`）
  - サイズ: `defense_revenue_yen` の対数
  - 色: `country`（ISOコードでマッピング）
  - 形状: 国内企業=円、海外=四角
- **エッジ**: `supply_chain` + `procurement` から構築
  - 太さ: 取引金額の対数
  - 色: 部品供給=グレー、共同開発=青、競合=赤
- **クラスタリング**: Force-simulation で国内防衛産業の生態系を可視化
- **パフォーマンス**: 企業数200社程度想定。Web Workerでフォースシミュレーションを別スレッド実行

### 5.7 基地配置マップ（v2.0新規追加）

別ビューとして提供。2Dマップ（Leaflet/OpenLayers）と3Dマップの両方:
- **2D**: 日本地図上に基地をマーカー表示。クリックで配備装備品一覧
- **3D**: 3DマップのXYZ空間に基地座標を追加軸として表示（オプション）
- **データ**: `location` テーブルの緯度経度を使用
- **フィルタ**: 都道府県別、自衛隊種別で絞り込み

---

## 6. インタラクション設計

### 6.1 UI/UX要件と優先度

| 機能 | 動作 | 優先度 | Phase |
|------|------|--------|-------|
| 装備品クリック | 詳細パネル表示（性能、調達史、出典リンク） | P0 | Phase 3 |
| 年度スライダー | 時点指定で保有装備フィルタ | P0 | Phase 4 |
| カテゴリフィルタ | 航空機/艦船/陸上/誘導武器の表示ON/OFF | P0 | Phase 3 |
| ツールチップ | ホバーで基本情報（名称、単価、年度）を表示 | P0 | Phase 3 |
| 出典表示 | 各データポイントに出典アイコン、クリックでsource詳細 | P0 | Phase 3 |
| メーカーフィルタ | チェックボックスで表示企業を絞り込み | P1 | Phase 4 |
| 予算規模フィルタ | 金額スライダー（対数）で下限・上限を設定 | P1 | Phase 4 |
| 国産/海外フィルタ | ラジオボタンで切り替え | P1 | Phase 4 |
| 検索 | 装備品名・メーカー名・型式で全文検索（trigram） | P1 | Phase 4 |
| 基地配置トグル | 3Dマップに基地配置情報をオーバーレイ表示 | P1 | Phase 5 |
| エクスポート | 現在のビューをPNG/SVGで保存 | P2 | Phase 6 |
| 共有 | URLにフィルタ状態・カメラ位置を含めて共有可能 | P2 | Phase 6 |
| VR/AR対応 | WebXR対応（将来的な拡張） | P3 | Phase 6以降 |

### 6.2 詳細パネルの構成

```
┌─────────────────────────┐
│ [3Dモデル or 画像]       │
│ 装備品正式名称           │
│ 型式 / NATO名称 / 別名   │
│ [国産/海外] [運用状況]   │
├─────────────────────────┤
│ 基本性能                │
│ - 全長: 15.7m          │
│ - 全幅: 10.7m          │
│ - 全高: 4.4m           │
│ - 重量: 13,154kg       │
│ - 乗員: 1名            │
│ - 最高速度: Mach 1.6   │
│ - レーダー: AESA       │
├─────────────────────────┤
│ 調達履歴（時系列表）     │
│ 年度 | 数量 | 単価(億円)│
│ 2011 |   4  |   102    │
│ 2020 | 105  |   143    │
│ 2025 |   8  |   143    │
├─────────────────────────┤
│ 予算推移（ミニ折れ線）   │
│ [■■■■■■■■■■]           │
├─────────────────────────┤
│ 基地配置                │
│ - 三沢基地: 26機        │
│ - 百里基地: 8機         │
├─────────────────────────┤
│ 部品構成（折りたたみ）   │
│ ▼ F-35A                │
│  ├─ エンジン (P&W F135) │
│  ├─ レーダー (三菱電機)  │
│  └─ ...                │
├─────────────────────────┤
│ 戦略文脈                │
│ 「中国・ロシアの第5世代  │
│  戦闘機に対する対抗能力」│
├─────────────────────────┤
│ 関連ニュース（最新3件）  │
│ - [2025-03-15] 緊急着陸 │
│ - [2025-01-20] 追加調達 │
├─────────────────────────┤
│ 出典リンク              │
│ [防衛白書2025 p.258]   │
│ [FY2026予算書]         │
│ [防衛装備庁契約結果]    │
└─────────────────────────┘
```

### 6.3 URL状態永続化（v2.0新規追加）

フィルタ状態・カメラ位置をURLクエリパラメータにエンコードし、共有可能にする。

```
https://example.com/map?
  year=2025                    // 年度スライダー位置
  &categories=aircraft,naval    // 表示カテゴリ（カンマ区切り）
  &manufacturers=mitsubishi,kawasaki // メーカーフィルタ
  &min_budget=1e10             // 予算下限（円）
  &max_budget=1e13             // 予算上限（円）
  &origin=domestic,joint       // 国産/共同/海外
  &camera=12.5,8.3,45.2,-0.3,0.1,5.0 // x,y,z,rotX,rotY,zoom
  &selected=F35A-001           // 選択中の装備品ID
```

---

## 7. 技術スタック詳細

| レイヤ | 技術 | 選定理由 | 代替案 |
|--------|------|---------|--------|
| **データ収集** | Python 3.12 + Scrapy + pdfplumber + pytesseract | PDF表抽出に強い。既存の防衛省文書処理実績 | Camelot（表抽出） |
| **NLP構造化** | SPECA/docs2formalspec パイプライン | NyxFoundation内既存資産。文書→構造化の自動化 | spaCy + 独自ルール |
| **DB** | PostgreSQL 15+ + pg_trgm + JSONB | 正規化と柔軟性の両立。全文検索・GIS拡張（PostGIS） | SQLite（小規模時）、MySQL |
| **キャッシュ** | Redis 7 | 頻繁アクセスの時系列データ・3Dモデルメタデータのキャッシュ | なし（直接DB） |
| **API層** | FastAPI (Python) + Pydantic v2 | 型安全、自動OpenAPI文書生成、async対応 | Django REST, Express |
| **3Dエンジン** | Three.js r165 (WebGL 2.0) | ブラウザ標準。Visuallyの基盤技術 | Babylon.js |
| **フロントエンド** | React 18 + TypeScript 5.4 | 型安全、コンポーネント再利用 | Vue, Svelte |
| **3D React統合** | React Three Fiber v8 + drei | Three.jsをReactの宣言的パラダイムで記述 | 純Three.js |
| **状態管理** | Zustand 4.5 | 軽量、TypeScriptとの相性良好、永続化プラグインあり | Redux Toolkit, Jotai |
| **2D可視化** | D3.js v7 | 予算推移グラフ、ネットワークグラフ | Chart.js, Recharts |
| **2Dマップ** | Leaflet 1.9（基地配置表示） | 軽量、日本向けタイルサーバー対応 | MapLibre, OpenLayers |
| **ルーティング** | React Router v6 | URL状態永続化の基盤 | Wouter |
| **スタイリング** | Tailwind CSS 3.4 + shadcn/ui | ユーティリティファースト、ダークモード対応 | Chakra UI |
| **開発環境** | Docker + docker-compose + devcontainer | 再現性のある環境構築 | Podman |
| **テスト** | pytest（API）+ Playwright（E2E）+ Vitest（Unit） | 統合テストとユニットテストの両立 | Jest |
| **ホスティング** | Cloudflare Pages（静的）+ Cloudflare Workers（APIエッジ） | CDN配信、エッジでのSSR | Vercel + Neon |

---

## 8. 実装フェーズ（ロードマップ）

### Phase間の依存関係グラフ

```
Phase 0: 基盤構築
    │
    ├──→ Phase 1: データレジストリ構築 ─┐
    │                                    │
    ├──→ Phase 2: 収集パイプライン構築 ─┤
    │                                    │
    └──→ Phase 3: 3D可視化MVP ──────────┤
         （並列開始可能）                 │
                                        ▼
                              Phase 4: 時系列・インタラクション
                                        │
                                        ├──→ Phase 5: サプライチェーン・拡張機能
                                        │
                                        └──→ Phase 6: 公開・運用
```

### Phase 0: 基盤構築（2週間）
- [ ] プロジェクトリポジトリ作成（`grandchildrice/mod-equipment-map` 等）
- [ ] Docker環境構築（PostgreSQL 15 + Redis 7 + API + Frontend）
- [ ] DBスキーママイグレーション（Alembic/SQLAlchemy）作成
- [ ] CI/CDパイプライン構築（GitHub Actions: lint, test, build）
- [ ] 開発環境ドキュメント整備
- **MVP定義**: `docker compose up` で全サービスが起動し、ヘルスチェックAPIが応答する

### Phase 1: データレジストリ構築（4週間）
- [ ] `source` テーブル設計実装（溯源基盤）
- [ ] `category` 階層データ投入（4大カテゴリ×3階層）
- [ ] `equipment_spec_schema` 初期スキーマ投入（戦闘機、護衛艦、戦車、誘導弾）
- [ ] `equipment` マスタ初期データ投入（防衛白書2025から主要装備品20件）
- [ ] `manufacturer` 初期データ投入（国内主要防衛企業15社）
- [ ] `equipment_timeline` 初期データ投入（2020-2025年の主要装備品）
- [ ] データ品質チェックパイプライン構築（pytestベースの整合テスト）
- **MVP定義**: DBに主要装備品20件が投入され、API経由で検索・取得可能
- **検証基準**: 全レコードが `source_id` を持つ。重複なし。カテゴリ階層が4階層まで正しく構築されている

### Phase 2: 収集パイプライン構築（4週間、Phase 0完了後に並列開始可）
- [ ] 予算書PDFパーサー実装（pdfplumber + 正規表現）
- [ ] 防衛白書PDFパーサー実装（表抽出 + OCRフォールバック）
- [ ] 防衛装備庁調達情報スクレイピング実装（Scrapy + Playwright for JS）
- [ ] 機密情報検出フィルタ実装（キーワード + 文書分類モデル）
- [ ] SPECA/docs2formalspec連携（構造化API呼び出し）
- [ ] `equipment.specs_json` スキーマバリデーション実装
- [ ] 自動実行スケジュール設定（GitHub Actions cron: 毎月1日）
- **MVP定義**: FY2025予算書から5件以上の装備品調達情報を自動抽出しDBに投入
- **検証基準**: 抽出した金額が原文と±5%以内。機密マーク検出の誤検出率<1%

### Phase 3: 3D可視化MVP（4週間、Phase 0完了後に並列開始可）
- [ ] Three.js基本シーン構築（ダークテーマ背景 #0A0A0F）
- [ ] 装備品ノード配置ロジック（X=年度, Y=log(予算), Z=カテゴリ）
- [ ] LOD制御実装（距離に応じた詳細度切り替え）
- [ ] カテゴリ別形状レンダリング（△□○♦）
- [ ] カメラ操作（OrbitControls + パン + ズーム）
- [ ] クリック→詳細パネル表示（Reactコンポーネント）
- [ ] カテゴリフィルタ実装（チェックボックスUI）
- [ ] ツールチップ実装（ホバー表示）
- [ ] FPSモニタリング（rstats.js）
- **MVP定義**: ブラウザで20件の装備品ノードが表示され、クリックで詳細パネルが開く
- **検証基準**: デスクトップで60fps維持。20ノードでLOD 0表示時も30fps以上

### Phase 4: 時系列・インタラクション（3週間）
- [ ] 年度スライダー実装（2000-2035年、1年刻み）
- [ ] アニメーションプレイバック（再生/一時停止/停止）
- [ ] メーカーフィルタ実装（チェックボックスリスト）
- [ ] 予算規模フィルタ実装（対数スライダー）
- [ ] 国産/海外/共同フィルタ実装
- [ ] 全文検索実装（pg_trgm連携API）
- [ ] URL状態永続化（クエリパラメータエンコード/デコード）
- [ ] HUD累積情報表示
- **MVP定義**: 年度スライダー操作で装備品のフェードイン/アウトが動作する
- **検証基準**: スライダー操作時のFPS低下が10%以内。URLコピー→貼り付けで同じ状態が復元される

### Phase 5: サプライチェーン・拡張機能（3週間）
- [ ] `supply_chain` データ投入（F-35A等の主要装備品5件分）
- [ ] メーカーネットワーク可視化（Force-directed graph）
- [ ] 予算フロー桑線グラフ（Sankey diagram）
- [ ] 基地配置マップ連携（Leaflet + 3Dオーバーレイ）
- [ ] `strategic_context` データ投入（防衛大綱・中期防衛から引用）
- [ ] `news_article` データ投入（RSSフィード連携）
- [ ] 2Dダッシュボード（D3.js: 予算推移、保有数推移）
- **MVP定義**: F-35Aの部品構成ツリーが表示され、エンジン（P&W）をクリックでその詳細に遷移する
- **検証基準**: サプライチェーンビューで50ノード/100エッジを60fpsで描画

### Phase 6: 公開・運用（2週間）
- [ ] パフォーマンス最適化（InstancedMesh、視錐台カリング、テクスチャ圧縮）
- [ ] 3Dモデルアセット最適化（glTF-TransformでDraco圧縮）
- [ ] アクセシビリティ対応（キーボードナビゲーション、ARIAラベル）
- [ ] モバイル対応（タッチ操作、画面回転）
- [ ] ドキュメント整備（README、API仕様書、ユーザーガイド）
- [ ] セキュリティレビュー（CSPヘッダー、機密情報漏洩チェック）
- [ ] 公開デプロイ（Cloudflare Pages）
- [ ] 監視ダッシュボード構築（収集パイプラインの成功率、DBサイズ）
- **MVP定義**: 公開URLでアクセス可能。機密情報が一切含まれていないことを最終確認
- **検証基準**: Lighthouseスコア Performance≥70, Accessibility≥90。収集パイプライン成功率≥95%

**総工期見込み: 約5ヶ月（Phase 1-3を並列で2ヶ月、その後Phase 4-6を逐次3ヶ月）**

---

## 9. テスト戦略（v2.0新規追加）

各Phaseの品質保証を明示する。

| テスト層 | 対象 | ツール | Phase |
|---------|------|--------|-------|
| **ユニットテスト** | DBモデル、パーサー関数、座標計算ロジック | pytest + pytest-cov | 全Phase |
| **統合テスト** | APIエンドポイント、DB→API→フロントのデータフロー | pytest + httpx + testcontainers | Phase 1, 3 |
| **E2Eテスト** | ブラウザ操作（クリック→パネル表示、スライダー→アニメーション） | Playwright | Phase 3, 4 |
| **視覚回帰テスト** | 3Dレンダリング結果のスクリーンショット比較 | Playwright + pixelmatch | Phase 3, 4 |
| **データ品質テスト** | 金額整合、年度整合、重複検出 | pytest + Great Expectations | Phase 1, 2 |
| **セキュリティテスト** | 機密情報混入チェック、XSS、CSP | 独自スクリプト + OWASP ZAP | Phase 2, 6 |
| **パフォーマンステスト** | FPS測定、メモリ使用量、ロード時間 | Lighthouse + rstats.js | Phase 3, 6 |
| **負荷テスト** | 同時接続100ユーザー想定 | k6 | Phase 6 |

---

## 10. リスクと対策（v2.0改訂）

| リスク | 影響度 | 確率 | 対策 | 監視指標 |
|--------|--------|------|------|---------|
| 防衛省サイト構造変更でスクレイピング失敗 | 高 | 中 | 収集コードをモジュール化（1ソース1モジュール）。構造変更時の影響を限定。XPath/CSS Selectorを設定ファイル化 | 収集成功率の日次監視。失敗時Slack通知 |
| PDFフォーマット変更でパース失敗 | 高 | 高 | バージョン管理（`source.file_hash`）。フォールバックとしてOCRルートを保持。テンプレートマッチング + MLハイブリッド | 抽出成功率、空の表の検出 |
| 3Dモデルデータが多すぎてブラウザが重い | 中 | 中 | LOD制御（4段階）、InstancedMesh、視錐台カリング、テクスチャ圧縮（Draco/Basis）。目標FPSを定量化 | FPSモニタリング。30fps未満で自動LOD上昇 |
| 装備品データの不整合・矛盾 | 中 | 高 | `source` テーブルによる溯源。複数ソース間の自動比較（同一装備品の単価が±20%を超える場合警告）。手動レビューフラグ | 矛盾検出レポートの週次生成 |
| 海外メーカー情報の英語表記統一 | 低 | 中 | `manufacturer` の `name` と `name_jp` の分離。正規化名マスタ（`canonical_name` フィールド）。ISO 3166国コード統一 | 重複企業レコードの検出 |
| 予算の「項」と装備品の紐付け曖昧性 | 中 | 高 | `budget.equipment_id` はNULL許容。紐付けできない場合は `line_item_name` のみ記録。後から手動レビューで紐付け | NULL率の監視。目標: 80%以上を紐付け |
| 機密情報混入の誤認 | **最高** | 低 | 収集対象を公開URLのみに限定。収集前にURLドメインをホワイトリスト化。機密マーク検出パイプライン。全データの人間レビュー（Phase 6まで） | 機密検出アラート数（目標: 0） |
| JSON Schema変更による過去データ互換性喪失 | 中 | 低 | `equipment_spec_schema` のバージョン管理。過去バージョンのスキーマを保持。マイグレーションスクリプト | スキーマバリデーション失敗率 |
| 開発期間の延長 | 中 | 中 | PhaseごとにMVPと検証基準を定義。並列作業で工期短縮。Phase 3-4はPhase 1の完了を待たずにモックデータで先行開始 | 各Phaseの実績工数と予定工数の比較 |

---

## 11. 参考リンク・ソース

### 一次情報源（防衛省・政府）
1. **防衛省 予算概算要求**: https://www.mod.go.jp/j/budget/
2. **防衛省 歳出決算**: https://www.mod.go.jp/j/budget/
3. **防衛白書**: https://www.mod.go.jp/j/publication/wp/
4. **防衛装備庁**: https://www.mod.go.jp/atla/
5. **防衛省 入札情報**: https://www.mod.go.jp/j/procurement/
6. **防衛大綱・中期防衛力整備計画**: https://www.mod.go.jp/j/policy/
7. **外務省 防衛装備移転三原則**: https://www.mofa.go.jp/mofaj/gaiko/
8. **財務省 為替レート**: https://www.mof.go.jp/policy/international_policy/reference/fx_rates/
9. **内閣官房 国家安全保障局**: https://www.cas.go.jp/jp/gaiyou/jimu/nss.html

### 類似プロジェクト・データベース
10. **SIPRI Arms Transfers Database**: https://www.sipri.org/databases/armstransfers — 国際的な武器移転データベース。国・年度・装備品の構造化パターンの参考
11. **Global Firepower**: https://www.globalfirepower.com/ — 各国軍事力ランキング。装備品カテゴリ分類の参考
12. **IISS Military Balance**: https://www.iiss.org/publications/military-balance — 年鑑形式の各国軍事力データ
13. **Wikipedia 自衛隊装備品一覧**: https://ja.wikipedia.org/wiki/自衛隊の装備品一覧 — 装備品名・型式の参考（一次資料優先だが名称確認用）

### 技術・ライブラリ
14. **pdfplumber**: https://github.com/jsvine/pdfplumber — PDFテーブル抽出
15. **Tesseract OCR**: https://github.com/tesseract-ocr/tesseract — 日本語OCRエンジン
16. **SPECA/docs2formalspec**: https://github.com/NyxFoundation/docs2formalspec — NLP構造化パイプライン
17. **Visually-3D**: https://github.com/NyxFoundation/visually-3d — 3D可視化CLIツール
18. **Three.js**: https://threejs.org/ — WebGL 3Dライブラリ
19. **React Three Fiber**: https://docs.pmndrs.react-three-fiber.org/ — Three.jsのReactラッパー
20. **Drei**: https://github.com/pmndrs/drei — React Three Fiber用ユーティリティ集
21. **Leaflet**: https://leafletjs.com/ — 軽量2Dマップライブラリ
22. **PostgreSQL pg_trgm**: https://www.postgresql.org/docs/current/pgtrgm.html — トリグラム全文検索

### 防衛産業・企業情報
23. **防衛産業参入促進ポータル**: https://www.mod.go.jp/atla/soubiseisaku_newentry.html
24. **防衛生産基盤強化法**: 防衛装備庁サイト内
25. **防衛装備庁 調達情報**: https://www.mod.go.jp/atla/choutatsu.html

### 標準・規格
26. **NATO STANAG 2014**: NATO標準化協定（装備品分類）
27. **ISO 3166-1**: 国コード標準
28. **JSON Schema Draft 2020-12**: https://json-schema.org/draft/2020-12 — specs_jsonの型定義

---

## 12. 付録

### 12.1 用語集

| 用語 | 説明 |
|------|------|
| **FMS** | Foreign Military Sales。日本政府が米国政府を通じて装備品を購入する制度。無償資金（GSA）と有償資金（FMS）がある |
| **防衛大綱** | 防衛省が策定する防衛力の整備方針（約10年ごとに見直し） |
| **中期防衛力整備計画** | 防衛大綱に基づく5年間の具体的装備整備計画 |
| **国家防衛戦略** | 2022年に新設。防衛大綱と並ぶ戦略文書 |
| **歳出化経費** | 予算編成上、各年度に計上される経費のこと。対義語は「義務的経費」（人件費等） |
| **随意契約** | 競争なしで特定の相手方と結ぶ契約。防衛装備ではFMS等で多用 |
| **指名競争** | 複数社を指名して行う競争入札。防衛装備で一般的 |
| **主契約者 (Prime)** | 防衛省と直接契約する企業。下請け（Sub）とは区別される |
| **防衛白書** | 防衛省が毎年発行する防衛政策・軍事力の年次報告書 |
| **LOM** | Letter of Offer and Acceptance。FMSにおける米国からの売渡申出書 |
| **AESA** | Active Electronically Scanned Array。能動電子走査アレイレーダー |
| **VLO** | Very Low Observable。極めて低い被探知性（ステルス性） |
| **LOD** | Level of Detail。詳細度。3Dモデルの距離に応じた表示精度切り替え |

### 12.2 データベース初期投入優先リスト

Phase 1で優先的に投入すべき装備品（防衛白書2025「自衛隊の主な装備」より）:

| 装備品 | 型式 | カテゴリ | 自衛隊種別 | 優先理由 |
|--------|------|---------|-----------|---------|
| F-35A | F-35A | 戦闘機 | 航空自衛隊 | 最大調達額、時系列データ豊富 |
| F-2 | F-2A/B | 戦闘機 | 航空自衛隊 | 国産開発、後継機問題 |
| P-1 | P-1 | 哨戒機 | 海上自衛隊 | 国産開発、大規模調達 |
| いずも型護衛艦 | DDH-183/184 | 護衛艦 | 海上自衛隊 | 空母化改修、話題性 |
| そうりゅう型潜水艦 | SS-501〜 | 潜水艦 | 海上自衛隊 | 高単価、国産技術 |
| たいげい型潜水艦 | SS-513〜 | 潜水艦 | 海上自衛隊 | 最新鋭、リチウム電池 |
| 10式戦車 | 10式 | 戦闘車両 | 陸上自衛隊 | 国産、高単価 |
| 16式機動戦闘車 | 16式MCV | 戦闘車両 | 陸上自衛隊 | 島嶼防衛、新装備 |
| 12式地対艦誘導弾 | 12式SSM | 対艦ミサイル | 陸上/海上自衛隊 | 射程延長型開発中 |
| AIM-120 AMRAAM | AIM-120 | 空対空ミサイル | 航空自衛隊 | FMS調達、継続的更新 |

---

*本設計書は Issue #30 の要件に基づき作成。v2.0ではセルフレビューによりデータレジストリの網羅性、セキュリティガードレール、MVP定義、型安全性、具体例を追加した。実装に際しては各Phaseごとに詳細設計を別途作成する。*
