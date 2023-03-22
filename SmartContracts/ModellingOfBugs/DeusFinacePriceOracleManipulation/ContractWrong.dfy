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

import opened NonNativeTypes



/** Provide a balance. */
trait {:termination false} ERC20 {
  /** Balance of the account. */
  var balances : map<ERC20 , uint128>;


}

/** A user account. */
class IERC20 extends ERC20 {

  constructor(initialBal: map<ERC20 , uint128>)
    ensures balances == initialBal
  {
    balances := initialBal;

  }

  method balanceOf(account : ERC20)  returns (b: uint128)

  {
    b := if account in balances then balances[account] else 0;
  }

  method transferFrom(from : ERC20, to : ERC20, amount : uint128)
    requires from in balances
    requires balances[from] >= amount
  {
    balances := balances[from := balances[from] - amount];
    balances := balances[to:= (if to in balances then balances[to] else 0) + amount];
  }
}

class UniswapV2Pair {
  var token0 : IERC20, token1 : IERC20, reserve0 : uint128, reserve1 : uint128
  constructor(t0 : IERC20, t1 : IERC20, r0 : uint128, r1 : uint128)
    ensures t0 == token0
    ensures t1 == token1
    ensures r0 == reserve0
    ensures r1 == reserve1
  {
    token0, token1, reserve0, reserve1:= t0, t1, r0, r1;
  }


}

