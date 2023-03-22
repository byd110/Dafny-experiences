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
include "./Token.dfy"

import opened NonNativeTypes

// datatype Msg = Msg(sender: Account, value: uint256)

// type Address = Account

class LendingContract  {
  var WETH : Token;
  var USDC : Token;
  ghost var WETHBanlance : nat;
  ghost var USDCBanlance : nat;
  ghost var inv : nat;
  var pair : map<Token, uint256>; // USDC - WETH
  // debt --> USDC, collateral --> WETH
  var debt : map<Address , uint256>;
  var collateral : map<Address , uint256>;

  predicate Ginv()
    reads this`WETHBanlance, this`USDCBanlance, this`inv
    requires WETHBanlance as nat * USDCBanlance as nat <= MAX_UINT256
  {
    WETHBanlance * USDCBanlance == inv
  }

  method liquidate(user : Address, msg: Msg) returns(g1: nat, g2 : nat)
    requires user in debt
    requires user in collateral
    requires USDC in pair
    requires WETH in pair
    requires 

    // requires Ginv()

    // modifies this

    // ensures Ginv()


  {
    var dAmount : uint256  := debt[user];
    var cAmount : uint256  := collateral[user];
    var price : uint256 := getPrice();
    if (price as nat * cAmount as nat < MAX_UINT256 && price * cAmount / 100 * 80 < dAmount && cAmount >= 0)
    { g1 := USDC.transfer(msg.sender, USDC, dAmount, msg, MAX_UINT256);
      g2 := WETH.transfer(WETH, msg.sender, cAmount, msg, MAX_UINT256);
    }
  }

  method getPrice() returns (c : uint256)
    requires USDC in pair
    requires WETH in pair
  {
    c := if (pair[USDC] != 0 && pair[WETH] != 0 )then pair[USDC]/ pair[WETH] else 0 ;// also need to consider the case of zeros in balances
  }

  constructor(w: Token, u : Token, p : map<Token , uint256>, d: map<Address , uint256>, c : map<Address , uint256>, usdcinitial : uint256, wethinitial : uint256)
    ensures  USDC in pair
    ensures  WETH in pair
  {
    WETH, USDC, debt, collateral := w, u,  d, c;
    pair := p[w := usdcinitial][u := usdcinitial];
  }
}

