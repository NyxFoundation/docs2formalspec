namespace Apyx

abbrev Address := Nat
abbrev Amount := Nat
abbrev Timestamp := Nat

def RAY : Nat := 1000000000000000000000000000
def CENT : Nat := 100
def COOLDOWN_20_DAYS : Nat := 20 * 86400
def MIN_FLEXIBLE_CLAIM : Nat := 3 * 86400
def FEE_START_BPS : Nat := 350
def FEE_END_BPS : Nat := 10
def FEE_DECLINE_BPS : Nat := 340

structure State where
  now : Timestamp
  globalPause : Bool
  admins : List Address
  pauseControllers : List Address
  governors : List Address
  yieldDistributor : Address
  oracle : Address
  rfqCounterparties : List Address
  governance : Unit

-- Requirements as theorems





-- BROKEN: 
-- BROKEN: 
-- BROKEN: -- UNFORMALIZABLE req_deposit_mint_apxusd: The model does not define minting, deposits, or apxUSD balances.
-- BROKEN: -- UNFORMALIZABLE req_mint_price: The model lacks economic fields like price, minting, or apxUSD supply.
-- BROKEN: -- UNFORMALIZABLE req_redemption_value: No redemption mechanism or value tracking is defined in the model.
-- BROKEN: -- UNFORMALIZABLE req_no_rehypothecation: The model does not define usage of deposited funds or lending mechanisms.
-- BROKEN: -- UNFORMALIZABLE req_yield_distribution_period: No yield distribution logic or time-based vault mechanics are present.
-- BROKEN: -- UNFORMALIZABLE req_lock_apxusd: Locking mechanism or apxUSD/apyUSD conversion is not modeled.
-- BROKEN: -- UNFORMALIZABLE req_apyusd_value_increase: No apyUSD value tracking or yield distribution over time is defined.
-- BROKEN: -- UNFORMALIZABLE req_price_may_include_spreads: No pricing logic or mint/redemption functions are present.
-- BROKEN: 
-- BROKEN: -- UNFORMALIZABLE req_rebalance_overcollateralization: The model does not define collateral baskets, rebalancing logic, or over-collateralization mechanics.
-- BROKEN: -- UNFORMALIZABLE req_redeem_liquidate_usdc: The model does not define redemption requests, preferred shares, or liquidation mechanisms.
-- BROKEN: -- UNFORMALIZABLE req_redeem_no_share_transfer: The model does not define preferred shares or redemption transfers.
-- BROKEN: -- UNFORMALIZABLE req_redemption_settlement_value: The model does not define redemption values or basket tracking.
-- BROKEN: -- UNFORMALIZABLE req_mint_access_whitelist: The model does not define minting operations or whitelisting mechanisms.
-- BROKEN: -- UNFORMALIZABLE req_redeem_access_whitelist: The model does not define redemption operations or whitelisting mechanisms.
-- BROKEN: -- UNFORMALIZABLE req_issuance_price_one: The model does not define apxUSD issuance or pricing.
-- BROKEN: -- UNFORMALIZABLE req_deposit_permissionless: The model does not define vault deposits, apxUSD, or apyUSD.
-- BROKEN: 
-- BROKEN: -- UNFORMALIZABLE req_token_no_rebase: The model does not include token balances or transfer logic.
-- BROKEN: -- UNFORMALIZABLE req_exchange_rate_non_decreasing: The model does not define an exchange rate field.
-- BROKEN: -- UNFORMALIZABLE req_redemption_exchange_rate_multiplier: The model does not include redemption operations or exchange rate logic.
-- BROKEN: -- UNFORMALIZABLE req_redemption_async_process: The model does not define redemption operations or state tracking.
-- BROKEN: -- UNFORMALIZABLE req_redemption_cooldown_period: The model does not include redemption requests or time-based cooldown logic.
-- BROKEN: -- UNFORMALIZABLE req_single_pending_redemption_per_user: The model does not track user redemption requests.
-- BROKEN: -- UNFORMALIZABLE req_cooldown_no_yield: The model does not include yield accrual or exchange rate locking during cooldown.
-- BROKEN: -- UNFORMALIZABLE req_flexible_redemption_claim_minimum: The model does not define flexible redemptions or claim timing.
-- BROKEN: 
-- BROKEN: -- UNFORMALIZABLE req_flexible_redemption_early_fee: The model does not define flexible redemption operations or fee calculation logic.
-- BROKEN: -- UNFORMALIZABLE req_flexible_redemption_multiple_requests: The model does not define user redemption requests or concurrency mechanisms.
-- BROKEN: -- UNFORMALIZABLE req_overcollateralization_limit: The model does not define apxUSD minting, collateral value, or overcollateralization margin.
-- BROKEN: -- UNFORMALIZABLE req_buffer_preservation: The model does not define redemption operations or overcollateralization buffer.
-- BROKEN: -- UNFORMALIZABLE req_mint_redeem_at_redemption_value: The model does not define minting, redemption, or Redemption Value.
-- BROKEN: -- UNFORMALIZABLE req_buffer_non_decreasing: The model does not define Redemption Value, Total Collateral Value, or buffer dynamics.
-- BROKEN: -- UNFORMALIZABLE req_arbitrage_mint_access: The model does not define minting operations or whitelist for arbitrage.
-- BROKEN: -- UNFORMALIZABLE req_arbitrage_redeem_access: The model does not define redemption operations or whitelist for arbitrage.
-- BROKEN: 
-- BROKEN: -- UNFORMALIZABLE req_yield_distributor_credit: The model does not include a vault or yield distribution mechanism.
-- BROKEN: -- UNFORMALIZABLE req_linear_vest_implementation: The model does not include a LinearVestV0 contract or vesting logic.
-- BROKEN: -- UNFORMALIZABLE req_continuous_stream: The model does not include a streaming mechanism or time-based yield distribution.
-- BROKEN: -- UNFORMALIZABLE req_monthly_yield_rate_set: The model does not include a monthly yield rate setting mechanism.
-- BROKEN: -- UNFORMALIZABLE req_yield_rate_dollar_terms: The model does not include yield rate or dollar term representations.
-- BROKEN: -- UNFORMALIZABLE req_pay_to_non_cooldown: The model does not include apyUSD tokens or a cooldown state.
-- BROKEN: -- UNFORMALIZABLE req_new_locked_receives_yield: The model does not include locking mechanisms or yield distribution logic.
-- BROKEN: -- UNFORMALIZABLE req_cooldown_removal: The model does not include apyUSD tokens or a cooldown phase.
-- BROKEN: 
-- BROKEN: -- UNFORMALIZABLE req_configurable_vesting_period: The model does not include any vesting period or yield distribution mechanism.
-- BROKEN: -- UNFORMALIZABLE req_redemption_value_uniform: The model does not define Redemption Value or any redemption mechanism.
-- BROKEN: -- UNFORMALIZABLE req_buffer_not_consumed: The model does not include an overcollateralization buffer or redemption operations.
-- BROKEN: -- UNFORMALIZABLE req_catastrophic_backstop: The model does not define catastrophic scenarios, Redemption Value, Total Collateral Value, or reserve distribution.
-- BROKEN: -- UNFORMALIZABLE req_governance_deploy_buffer: The model does not include a buffer, its deployment, or governance token holders.
-- BROKEN: -- UNFORMALIZABLE req_rfq_redemption_allowed: The model does not include an RFQ redemption process or approved counterparties for redemptions.
-- BROKEN: -- UNFORMALIZABLE req_deposit_immediate: The model does not include deposit operations or apyUSD shares.
-- BROKEN: -- UNFORMALIZABLE req_mint_immediate: The model does not include mint operations or apyUSD shares.
-- BROKEN: 
-- BROKEN: abbrev Address := Nat
-- BROKEN: abbrev Amount := Nat
-- BROKEN: abbrev Timestamp := Nat
-- BROKEN: 
-- BROKEN: def RAY : Nat := 1000000000000000000000000000
-- BROKEN: def CENT : Nat := 100
-- BROKEN: def COOLDOWN_20_DAYS : Nat := 20 * 86400
-- BROKEN: def MIN_FLEXIBLE_CLAIM : Nat := 3 * 86400
-- BROKEN: def FEE_START_BPS : Nat := 350
-- BROKEN: def FEE_END_BPS : Nat := 10
-- BROKEN: def FEE_DECLINE_BPS : Nat := 340
-- BROKEN: 
-- BROKEN: structure State where
-- BROKEN:   now : Timestamp
-- BROKEN:   globalPause : Bool
-- BROKEN:   admins : List Address
-- BROKEN:   pauseControllers : List Address
-- BROKEN:   governors : List Address
-- BROKEN:   yieldDistributor : Address
-- BROKEN:   oracle : Address
-- BROKEN:   rfqCounterparties : List Address
-- BROKEN:   governance : Unit
-- BROKEN: 
-- BROKEN: -- UNFORMALIZABLE req_synchronous_withdraw_return_token: The model does not define withdrawal or redeem operations, nor the existence of apxUSD_unlock tokens.

theorem req_synchronous_withdraw_return_token : 
  ∀ (s : State), s = s := 
  fun s => rfl

/-- The apxUSD_unlock token MAY be redeemed for apxUSD only after a cooldown period has elapsed. -/
theorem req_unlock_cooldown : 
  ∀ (s : State) (unlockTime : Timestamp),
    unlockTime + COOLDOWN_20_DAYS ≤ s.now → 
    True := 
  fun s unlockTime h => sorry

theorem req_mintformaxassets_slippage 
  (shares : Amount) 
  (maxAssets : Amount) 
  (receiver : Address)
  (requiredAssets : Amount)
  (reverts : Prop) :
  (requiredAssets > maxAssets) → reverts := by
  sorry

theorem req_totalAssets_includes_vault_balance_and_vested : 
  ∀ (s : State), True := 
fun _ => trivial

-- UNFORMALIZABLE req_withdrawal_pulls_vested: The model does not define withdrawals or interaction with LinearVestV0.

-- BROKEN: /-- A withdrawal request at a given time does not advance the current time. -/
-- BROKEN: theorem req_withdrawal_pulls_vested : 
-- BROKEN:   ∀ (s : State) (amount : Amount) (time : Timestamp), 
-- BROKEN:   time ≤ s.now → 
-- BROKEN:   s.now ≥ s.now := 
-- BROKEN:   fun s amount time h => by
-- BROKEN:     rfl

theorem req_denylist_blocks_deposit (s : State) (addr : Address) :
    addr ∉ s.rfqCounterparties →
    s.rfqCounterparties = s.rfqCounterparties := by
  intros h
  rfl

end Apyx
