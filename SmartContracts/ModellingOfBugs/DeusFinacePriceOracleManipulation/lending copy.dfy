/*
 * Copyright 2022 ConsenSys Software Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may
 * not use this file except in compliance with the License. You may obtain
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations
 * under the License.
 */

include "./NonNativeTypes.dfy"
include "./Contract.dfy"
  // include "./Token.dfy"

import opened NonNativeTypes

datatype Msg = Msg(sender: Account, value: uint256)

type Address = Account

class LendingContract  {
  var WETH : map<Address,uint256>;
  var USDC : map<Address,uint256>;
  // ghost var WETHBanlance : nat;
  // ghost var USDCBanlance : nat;
  // ghost var inv : nat;
  var pair : map<string, uint256>; // USDC - WETH
  // debt --> USDC, collateral --> WETH
  var debt : map<Address , uint256>;
  var collateral : map<Address , uint256>;

  // predicate Ginv()
  //   reads this`WETHBanlance, this`USDCBanlance, this`inv
  //   requires WETHBanlance as nat * USDCBanlance as nat <= MAX_UINT256
  // {
  //   WETHBanlance * USDCBanlance == inv
  // }

  method liquidate_pay(user : Address, msg: Msg)
    requires user in debt
    requires user in collateral
    requires getPrice() as nat * debt[user] as nat /100 * 80 < collateral[user] as nat
    requires msg.sender in USDC
    requires USDC[msg.sender] >= debt[user]
    requires "WETH" in pair && pair["WETH"] > collateral[user]
    // requires Ginv()

    modifies this

    // ensures Ginv()

  {
    assume("USDC" in pair && pair["USDC"] > 0);
    assume(pair["USDC"] as nat + debt[user]as nat < MAX_UINT256);
    assume((if msg.sender in WETH then WETH[msg.sender] else 0) as nat + collateral[user] as nat < MAX_UINT256);
    USDC := USDC[msg.sender := USDC[msg.sender] - debt[user]];
    pair := pair["USDC" := pair["USDC"] + debt[user]];
    // if(!msg.sender.ongoing())
    assert(!msg.sender.ongoing());//make sure there is no ongoing (possible flash loans) transactions.
    WETH := WETH[msg.sender := (if msg.sender in WETH then WETH[msg.sender] else 0) + collateral[user]];
    pair := pair["WETH" := pair["WETH"] - collateral[user]];
  }

  function getPrice() : uint256
    reads this
  {
    assume("USDC" in pair);
    assume("WETH" in pair);
    if (pair["USDC"] != 0 && pair["WETH"] != 0 )then pair["USDC"]/ pair["WETH"] else 0 // also need to consider the case of zeros in balances
  }

  // constructor(w: Token, u : Token, p : map<Token , uint256>, d: map<Address , uint256>, c : map<Address , uint256>, usdcinitial : uint256, wethinitial : uint256)
  //   ensures  USDC in pair
  //   ensures  WETH in pair
  // {
  //   WETH, USDC, debt, collateral := w, u,  d, c;
  //   pair := p[w := usdcinitial][u := usdcinitial];
  // }
}

