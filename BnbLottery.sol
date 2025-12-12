/**
 *Submitted for verification at BscScan.com on 2025-07-29
 */

/**
 *Submitted for verification at BscScan.com on 2025-07-24
 */

/**
 *Submitted for verification at testnet.bscscan.com on 2025-07-17
 */

/**
 *Submitted for verification at testnet.bscscan.com on 2025-07-16
 */

// Sources flattened with hardhat v2.24.2 https://hardhat.org

// SPDX-License-Identifier: MIT

// File @layerzerolabs/lz-evm-oapp-v2/contracts/oft/libs/OFTComposeMsgCodec.sol@v3.0.110

// Original license: SPDX_License_Identifier: MIT

pragma solidity ^0.8.20;

library OFTComposeMsgCodec {
    // Offset constants for decoding composed messages
    uint8 private constant NONCE_OFFSET = 8;
    uint8 private constant SRC_EID_OFFSET = 12;
    uint8 private constant AMOUNT_LD_OFFSET = 44;
    uint8 private constant COMPOSE_FROM_OFFSET = 76;

    /**
     * @dev Encodes a OFT composed message.
     * @param _nonce The nonce value.
     * @param _srcEid The source endpoint ID.
     * @param _amountLD The amount in local decimals.
     * @param _composeMsg The composed message.
     * @return _msg The encoded Composed message.
     */
    function encode(
        uint64 _nonce,
        uint32 _srcEid,
        uint256 _amountLD,
        bytes memory _composeMsg // 0x[composeFrom][composeMsg]
    ) internal pure returns (bytes memory _msg) {
        _msg = abi.encodePacked(_nonce, _srcEid, _amountLD, _composeMsg);
    }

    /**
     * @dev Retrieves the nonce from the composed message.
     * @param _msg The message.
     * @return The nonce value.
     */
    function nonce(bytes calldata _msg) internal pure returns (uint64) {
        return uint64(bytes8(_msg[:NONCE_OFFSET]));
    }

    /**
     * @dev Retrieves the source endpoint ID from the composed message.
     * @param _msg The message.
     * @return The source endpoint ID.
     */
    function srcEid(bytes calldata _msg) internal pure returns (uint32) {
        return uint32(bytes4(_msg[NONCE_OFFSET:SRC_EID_OFFSET]));
    }

    /**
     * @dev Retrieves the amount in local decimals from the composed message.
     * @param _msg The message.
     * @return The amount in local decimals.
     */
    function amountLD(bytes calldata _msg) internal pure returns (uint256) {
        return uint256(bytes32(_msg[SRC_EID_OFFSET:AMOUNT_LD_OFFSET]));
    }

    /**
     * @dev Retrieves the composeFrom value from the composed message.
     * @param _msg The message.
     * @return The composeFrom value.
     */
    function composeFrom(bytes calldata _msg) internal pure returns (bytes32) {
        return bytes32(_msg[AMOUNT_LD_OFFSET:COMPOSE_FROM_OFFSET]);
    }

    /**
     * @dev Retrieves the composed message.
     * @param _msg The message.
     * @return The composed message.
     */
    function composeMsg(
        bytes calldata _msg
    ) internal pure returns (bytes memory) {
        return _msg[COMPOSE_FROM_OFFSET:];
    }

    /**
     * @dev Converts an address to bytes32.
     * @param _addr The address to convert.
     * @return The bytes32 representation of the address.
     */
    function addressToBytes32(address _addr) internal pure returns (bytes32) {
        return bytes32(uint256(uint160(_addr)));
    }

    /**
     * @dev Converts bytes32 to an address.
     * @param _b The bytes32 value to convert.
     * @return The address representation of bytes32.
     */
    function bytes32ToAddress(bytes32 _b) internal pure returns (address) {
        return address(uint160(uint256(_b)));
    }
}

// File @layerzerolabs/lz-evm-protocol-v2/contracts/interfaces/ILayerZeroComposer.sol@v3.0.110

// Original license: SPDX_License_Identifier: MIT

pragma solidity >=0.8.0;

/**
 * @title ILayerZeroComposer
 */
interface ILayerZeroComposer {
    /**
     * @notice Composes a LayerZero message from an OApp.
     * @dev To ensure non-reentrancy, implementers of this interface MUST assert msg.sender is the corresponding EndpointV2 contract (i.e., onlyEndpointV2).
     * @param _from The address initiating the composition, typically the OApp where the lzReceive was called.
     * @param _guid The unique identifier for the corresponding LayerZero src/dst tx.
     * @param _message The composed message payload in bytes. NOT necessarily the same payload passed via lzReceive.
     * @param _executor The address of the executor for the composed message.
     * @param _extraData Additional arbitrary data in bytes passed by the entity who executes the lzCompose.
     */
    function lzCompose(
        address _from,
        bytes32 _guid,
        bytes calldata _message,
        address _executor,
        bytes calldata _extraData
    ) external payable;
}

// File contracts/Lock.sol

/**
 *Submitted for verification at amoy.polygonscan.com on 2025-06-12
 */

// Sources flattened with hardhat v2.24.2 https://hardhat.org

// Original license: SPDX_License_Identifier: MIT

// File @openzeppelin/contracts/utils/introspection/IERC165.sol@v5.3.0

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v5.1.0) (utils/introspection/IERC165.sol)

pragma solidity ^0.8.20;

/**
 * @dev Interface of the ERC-165 standard, as defined in the
 * https://eips.ethereum.org/EIPS/eip-165[ERC].
 *
 * Implementers can declare support of contract interfaces, which can then be
 * queried by others ({ERC165Checker}).
 *
 * For an implementation, see {ERC165}.
 */
interface IERC165 {
    /**
     * @dev Returns true if this contract implements the interface defined by
     * `interfaceId`. See the corresponding
     * https://eips.ethereum.org/EIPS/eip-165#how-interfaces-are-identified[ERC section]
     * to learn more about how these ids are created.
     *
     * This function call must use less than 30 000 gas.
     */
    function supportsInterface(bytes4 interfaceId) external view returns (bool);
}

// File @openzeppelin/contracts/interfaces/IERC165.sol@v5.3.0

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v5.0.0) (interfaces/IERC165.sol)

pragma solidity ^0.8.20;

// File @openzeppelin/contracts/token/ERC20/IERC20.sol@v5.3.0

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v5.1.0) (token/ERC20/IERC20.sol)

pragma solidity ^0.8.20;

/**
 * @dev Interface of the ERC-20 standard as defined in the ERC.
 */
interface IERC20 {
    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(
        address indexed owner,
        address indexed spender,
        uint256 value
    );

    /**
     * @dev Returns the value of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the value of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves a `value` amount of tokens from the caller's account to `to`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address to, uint256 value) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(
        address owner,
        address spender
    ) external view returns (uint256);

    /**
     * @dev Sets a `value` amount of tokens as the allowance of `spender` over the
     * caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 value) external returns (bool);

    /**
     * @dev Moves a `value` amount of tokens from `from` to `to` using the
     * allowance mechanism. `value` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address from,
        address to,
        uint256 value
    ) external returns (bool);
}

using SafeERC20 for IERC20;

// File @openzeppelin/contracts/interfaces/IERC20.sol@v5.3.0

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v5.0.0) (interfaces/IERC20.sol)

pragma solidity ^0.8.20;

// File @openzeppelin/contracts/interfaces/IERC1363.sol@v5.3.0

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v5.1.0) (interfaces/IERC1363.sol)

pragma solidity ^0.8.20;

/**
 * @title IERC1363
 * @dev Interface of the ERC-1363 standard as defined in the https://eips.ethereum.org/EIPS/eip-1363[ERC-1363].
 *
 * Defines an extension interface for ERC-20 tokens that supports executing code on a recipient contract
 * after `transfer` or `transferFrom`, or code on a spender contract after `approve`, in a single transaction.
 */
interface IERC1363 is IERC20, IERC165 {
    /*
     * Note: the ERC-165 identifier for this interface is 0xb0202a11.
     * 0xb0202a11 ===
     *   bytes4(keccak256('transferAndCall(address,uint256)')) ^
     *   bytes4(keccak256('transferAndCall(address,uint256,bytes)')) ^
     *   bytes4(keccak256('transferFromAndCall(address,address,uint256)')) ^
     *   bytes4(keccak256('transferFromAndCall(address,address,uint256,bytes)')) ^
     *   bytes4(keccak256('approveAndCall(address,uint256)')) ^
     *   bytes4(keccak256('approveAndCall(address,uint256,bytes)'))
     */

    /**
     * @dev Moves a `value` amount of tokens from the caller's account to `to`
     * and then calls {IERC1363Receiver-onTransferReceived} on `to`.
     * @param to The address which you want to transfer to.
     * @param value The amount of tokens to be transferred.
     * @return A boolean value indicating whether the operation succeeded unless throwing.
     */
    function transferAndCall(address to, uint256 value) external returns (bool);

    /**
     * @dev Moves a `value` amount of tokens from the caller's account to `to`
     * and then calls {IERC1363Receiver-onTransferReceived} on `to`.
     * @param to The address which you want to transfer to.
     * @param value The amount of tokens to be transferred.
     * @param data Additional data with no specified format, sent in call to `to`.
     * @return A boolean value indicating whether the operation succeeded unless throwing.
     */
    function transferAndCall(
        address to,
        uint256 value,
        bytes calldata data
    ) external returns (bool);

    /**
     * @dev Moves a `value` amount of tokens from `from` to `to` using the allowance mechanism
     * and then calls {IERC1363Receiver-onTransferReceived} on `to`.
     * @param from The address which you want to send tokens from.
     * @param to The address which you want to transfer to.
     * @param value The amount of tokens to be transferred.
     * @return A boolean value indicating whether the operation succeeded unless throwing.
     */
    function transferFromAndCall(
        address from,
        address to,
        uint256 value
    ) external returns (bool);

    /**
     * @dev Moves a `value` amount of tokens from `from` to `to` using the allowance mechanism
     * and then calls {IERC1363Receiver-onTransferReceived} on `to`.
     * @param from The address which you want to send tokens from.
     * @param to The address which you want to transfer to.
     * @param value The amount of tokens to be transferred.
     * @param data Additional data with no specified format, sent in call to `to`.
     * @return A boolean value indicating whether the operation succeeded unless throwing.
     */
    function transferFromAndCall(
        address from,
        address to,
        uint256 value,
        bytes calldata data
    ) external returns (bool);

    /**
     * @dev Sets a `value` amount of tokens as the allowance of `spender` over the
     * caller's tokens and then calls {IERC1363Spender-onApprovalReceived} on `spender`.
     * @param spender The address which will spend the funds.
     * @param value The amount of tokens to be spent.
     * @return A boolean value indicating whether the operation succeeded unless throwing.
     */
    function approveAndCall(
        address spender,
        uint256 value
    ) external returns (bool);

    /**
     * @dev Sets a `value` amount of tokens as the allowance of `spender` over the
     * caller's tokens and then calls {IERC1363Spender-onApprovalReceived} on `spender`.
     * @param spender The address which will spend the funds.
     * @param value The amount of tokens to be spent.
     * @param data Additional data with no specified format, sent in call to `spender`.
     * @return A boolean value indicating whether the operation succeeded unless throwing.
     */
    function approveAndCall(
        address spender,
        uint256 value,
        bytes calldata data
    ) external returns (bool);
}

// File @openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol@v5.3.0

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v5.3.0) (token/ERC20/utils/SafeERC20.sol)

pragma solidity ^0.8.20;

/**
 * @title SafeERC20
 * @dev Wrappers around ERC-20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeERC20 for IERC20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeERC20 {
    /**
     * @dev An operation with an ERC-20 token failed.
     */
    error SafeERC20FailedOperation(address token);

    /**
     * @dev Indicates a failed `decreaseAllowance` request.
     */
    error SafeERC20FailedDecreaseAllowance(
        address spender,
        uint256 currentAllowance,
        uint256 requestedDecrease
    );

    /**
     * @dev Transfer `value` amount of `token` from the calling contract to `to`. If `token` returns no value,
     * non-reverting calls are assumed to be successful.
     */
    function safeTransfer(IERC20 token, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeCall(token.transfer, (to, value)));
    }

    /**
     * @dev Transfer `value` amount of `token` from `from` to `to`, spending the approval given by `from` to the
     * calling contract. If `token` returns no value, non-reverting calls are assumed to be successful.
     */
    function safeTransferFrom(
        IERC20 token,
        address from,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(
            token,
            abi.encodeCall(token.transferFrom, (from, to, value))
        );
    }

    /**
     * @dev Variant of {safeTransfer} that returns a bool instead of reverting if the operation is not successful.
     */
    function trySafeTransfer(
        IERC20 token,
        address to,
        uint256 value
    ) internal returns (bool) {
        return
            _callOptionalReturnBool(
                token,
                abi.encodeCall(token.transfer, (to, value))
            );
    }

    /**
     * @dev Variant of {safeTransferFrom} that returns a bool instead of reverting if the operation is not successful.
     */
    function trySafeTransferFrom(
        IERC20 token,
        address from,
        address to,
        uint256 value
    ) internal returns (bool) {
        return
            _callOptionalReturnBool(
                token,
                abi.encodeCall(token.transferFrom, (from, to, value))
            );
    }

    /**
     * @dev Increase the calling contract's allowance toward `spender` by `value`. If `token` returns no value,
     * non-reverting calls are assumed to be successful.
     *
     * IMPORTANT: If the token implements ERC-7674 (ERC-20 with temporary allowance), and if the "client"
     * smart contract uses ERC-7674 to set temporary allowances, then the "client" smart contract should avoid using
     * this function. Performing a {safeIncreaseAllowance} or {safeDecreaseAllowance} operation on a token contract
     * that has a non-zero temporary allowance (for that particular owner-spender) will result in unexpected behavior.
     */
    function safeIncreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        uint256 oldAllowance = token.allowance(address(this), spender);
        forceApprove(token, spender, oldAllowance + value);
    }

    /**
     * @dev Decrease the calling contract's allowance toward `spender` by `requestedDecrease`. If `token` returns no
     * value, non-reverting calls are assumed to be successful.
     *
     * IMPORTANT: If the token implements ERC-7674 (ERC-20 with temporary allowance), and if the "client"
     * smart contract uses ERC-7674 to set temporary allowances, then the "client" smart contract should avoid using
     * this function. Performing a {safeIncreaseAllowance} or {safeDecreaseAllowance} operation on a token contract
     * that has a non-zero temporary allowance (for that particular owner-spender) will result in unexpected behavior.
     */
    function safeDecreaseAllowance(
        IERC20 token,
        address spender,
        uint256 requestedDecrease
    ) internal {
        unchecked {
            uint256 currentAllowance = token.allowance(address(this), spender);
            if (currentAllowance < requestedDecrease) {
                revert SafeERC20FailedDecreaseAllowance(
                    spender,
                    currentAllowance,
                    requestedDecrease
                );
            }
            forceApprove(token, spender, currentAllowance - requestedDecrease);
        }
    }

    /**
     * @dev Set the calling contract's allowance toward `spender` to `value`. If `token` returns no value,
     * non-reverting calls are assumed to be successful. Meant to be used with tokens that require the approval
     * to be set to zero before setting it to a non-zero value, such as USDT.
     *
     * NOTE: If the token implements ERC-7674, this function will not modify any temporary allowance. This function
     * only sets the "standard" allowance. Any temporary allowance will remain active, in addition to the value being
     * set here.
     */
    function forceApprove(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        bytes memory approvalCall = abi.encodeCall(
            token.approve,
            (spender, value)
        );

        if (!_callOptionalReturnBool(token, approvalCall)) {
            _callOptionalReturn(
                token,
                abi.encodeCall(token.approve, (spender, 0))
            );
            _callOptionalReturn(token, approvalCall);
        }
    }

    /**
     * @dev Performs an {ERC1363} transferAndCall, with a fallback to the simple {ERC20} transfer if the target has no
     * code. This can be used to implement an {ERC721}-like safe transfer that rely on {ERC1363} checks when
     * targeting contracts.
     *
     * Reverts if the returned value is other than `true`.
     */
    function transferAndCallRelaxed(
        IERC1363 token,
        address to,
        uint256 value,
        bytes memory data
    ) internal {
        if (to.code.length == 0) {
            safeTransfer(token, to, value);
        } else if (!token.transferAndCall(to, value, data)) {
            revert SafeERC20FailedOperation(address(token));
        }
    }

    /**
     * @dev Performs an {ERC1363} transferFromAndCall, with a fallback to the simple {ERC20} transferFrom if the target
     * has no code. This can be used to implement an {ERC721}-like safe transfer that rely on {ERC1363} checks when
     * targeting contracts.
     *
     * Reverts if the returned value is other than `true`.
     */
    function transferFromAndCallRelaxed(
        IERC1363 token,
        address from,
        address to,
        uint256 value,
        bytes memory data
    ) internal {
        if (to.code.length == 0) {
            safeTransferFrom(token, from, to, value);
        } else if (!token.transferFromAndCall(from, to, value, data)) {
            revert SafeERC20FailedOperation(address(token));
        }
    }

    /**
     * @dev Performs an {ERC1363} approveAndCall, with a fallback to the simple {ERC20} approve if the target has no
     * code. This can be used to implement an {ERC721}-like safe transfer that rely on {ERC1363} checks when
     * targeting contracts.
     *
     * NOTE: When the recipient address (`to`) has no code (i.e. is an EOA), this function behaves as {forceApprove}.
     * Opposedly, when the recipient address (`to`) has code, this function only attempts to call {ERC1363-approveAndCall}
     * once without retrying, and relies on the returned value to be true.
     *
     * Reverts if the returned value is other than `true`.
     */
    function approveAndCallRelaxed(
        IERC1363 token,
        address to,
        uint256 value,
        bytes memory data
    ) internal {
        if (to.code.length == 0) {
            forceApprove(token, to, value);
        } else if (!token.approveAndCall(to, value, data)) {
            revert SafeERC20FailedOperation(address(token));
        }
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     *
     * This is a variant of {_callOptionalReturnBool} that reverts if call fails to meet the requirements.
     */
    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        uint256 returnSize;
        uint256 returnValue;
        assembly ("memory-safe") {
            let success := call(
                gas(),
                token,
                0,
                add(data, 0x20),
                mload(data),
                0,
                0x20
            )
            // bubble errors
            if iszero(success) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0, returndatasize())
                revert(ptr, returndatasize())
            }
            returnSize := returndatasize()
            returnValue := mload(0)
        }

        if (
            returnSize == 0 ? address(token).code.length == 0 : returnValue != 1
        ) {
            revert SafeERC20FailedOperation(address(token));
        }
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     *
     * This is a variant of {_callOptionalReturn} that silently catches all reverts and returns a bool instead.
     */
    function _callOptionalReturnBool(
        IERC20 token,
        bytes memory data
    ) private returns (bool) {
        bool success;
        uint256 returnSize;
        uint256 returnValue;
        assembly ("memory-safe") {
            success := call(
                gas(),
                token,
                0,
                add(data, 0x20),
                mload(data),
                0,
                0x20
            )
            returnSize := returndatasize()
            returnValue := mload(0)
        }
        return
            success &&
            (
                returnSize == 0
                    ? address(token).code.length > 0
                    : returnValue == 1
            );
    }
}

// File chainlink/contracts/src/v0.8/shared/interfaces/IOwnable.sol@v2.25.0

// Original license: SPDX_License_Identifier: MIT
pragma solidity ^0.8.0;

interface IOwnable {
    function owner() external returns (address);

    function transferOwnership(address recipient) external;

    function acceptOwnership() external;
}

// File chainlink/contracts/src/v0.8/shared/access/ConfirmedOwnerWithProposal.sol@v2.25.0

// Original license: SPDX_License_Identifier: MIT
pragma solidity ^0.8.0;

/// @title The ConfirmedOwner contract
/// @notice A contract with helpers for basic contract ownership.
contract ConfirmedOwnerWithProposal is IOwnable {
    address private s_owner;
    address private s_pendingOwner;

    event OwnershipTransferRequested(address indexed from, address indexed to);
    event OwnershipTransferred(address indexed from, address indexed to);

    constructor(address newOwner, address pendingOwner) {
        // solhint-disable-next-line gas-custom-errors
        require(newOwner != address(0), "Cannot set owner to zero");

        s_owner = newOwner;
        if (pendingOwner != address(0)) {
            _transferOwnership(pendingOwner);
        }
    }

    /// @notice Allows an owner to begin transferring ownership to a new address.
    function transferOwnership(address to) public override onlyOwner {
        _transferOwnership(to);
    }

    /// @notice Allows an ownership transfer to be completed by the recipient.
    function acceptOwnership() external override {
        // solhint-disable-next-line gas-custom-errors
        require(msg.sender == s_pendingOwner, "Must be proposed owner");

        address oldOwner = s_owner;
        s_owner = msg.sender;
        s_pendingOwner = address(0);

        emit OwnershipTransferred(oldOwner, msg.sender);
    }

    /// @notice Get the current owner
    function owner() public view override returns (address) {
        return s_owner;
    }

    /// @notice validate, transfer ownership, and emit relevant events
    function _transferOwnership(address to) private {
        // solhint-disable-next-line gas-custom-errors
        require(to != msg.sender, "Cannot transfer to self");

        s_pendingOwner = to;

        emit OwnershipTransferRequested(s_owner, to);
    }

    /// @notice validate access
    function _validateOwnership() internal view {
        // solhint-disable-next-line gas-custom-errors
        require(msg.sender == s_owner, "Only callable by owner");
    }

    /// @notice Reverts if called by anyone other than the contract owner.
    modifier onlyOwner() {
        _validateOwnership();
        _;
    }
}

// File chainlink/contracts/src/v0.8/shared/access/ConfirmedOwner.sol@v2.25.0

// Original license: SPDX_License_Identifier: MIT
pragma solidity ^0.8.0;

/// @title The ConfirmedOwner contract
/// @notice A contract with helpers for basic contract ownership.
contract ConfirmedOwner is ConfirmedOwnerWithProposal {
    constructor(
        address newOwner
    ) ConfirmedOwnerWithProposal(newOwner, address(0)) {}
}

// File chainlink/contracts/src/v0.8/vrf/dev/interfaces/IVRFSubscriptionV2Plus.sol@v2.25.0

// Original license: SPDX_License_Identifier: MIT
pragma solidity ^0.8.0;

/// @notice The IVRFSubscriptionV2Plus interface defines the subscription
/// @notice related methods implemented by the V2Plus coordinator.
interface IVRFSubscriptionV2Plus {
    /**
     * @notice Add a consumer to a VRF subscription.
     * @param subId - ID of the subscription
     * @param consumer - New consumer which can use the subscription
     */
    function addConsumer(uint256 subId, address consumer) external;

    /**
     * @notice Remove a consumer from a VRF subscription.
     * @param subId - ID of the subscription
     * @param consumer - Consumer to remove from the subscription
     */
    function removeConsumer(uint256 subId, address consumer) external;

    /**
     * @notice Cancel a subscription
     * @param subId - ID of the subscription
     * @param to - Where to send the remaining LINK to
     */
    function cancelSubscription(uint256 subId, address to) external;

    /**
     * @notice Accept subscription owner transfer.
     * @param subId - ID of the subscription
     * @dev will revert if original owner of subId has
     * not requested that msg.sender become the new owner.
     */
    function acceptSubscriptionOwnerTransfer(uint256 subId) external;

    /**
     * @notice Request subscription owner transfer.
     * @param subId - ID of the subscription
     * @param newOwner - proposed new owner of the subscription
     */
    function requestSubscriptionOwnerTransfer(
        uint256 subId,
        address newOwner
    ) external;

    /**
     * @notice Create a VRF subscription.
     * @return subId - A unique subscription id.
     * @dev You can manage the consumer set dynamically with addConsumer/removeConsumer.
     * @dev Note to fund the subscription with LINK, use transferAndCall. For example
     * @dev  LINKTOKEN.transferAndCall(
     * @dev    address(COORDINATOR),
     * @dev    amount,
     * @dev    abi.encode(subId));
     * @dev Note to fund the subscription with Native, use fundSubscriptionWithNative. Be sure
     * @dev  to send Native with the call, for example:
     * @dev COORDINATOR.fundSubscriptionWithNative{value: amount}(subId);
     */
    function createSubscription() external returns (uint256 subId);

    /**
     * @notice Get a VRF subscription.
     * @param subId - ID of the subscription
     * @return balance - LINK balance of the subscription in juels.
     * @return nativeBalance - native balance of the subscription in wei.
     * @return reqCount - Requests count of subscription.
     * @return owner - owner of the subscription.
     * @return consumers - list of consumer address which are able to use this subscription.
     */
    function getSubscription(
        uint256 subId
    )
        external
        view
        returns (
            uint96 balance,
            uint96 nativeBalance,
            uint64 reqCount,
            address owner,
            address[] memory consumers
        );

    /*
     * @notice Check to see if there exists a request commitment consumers
     * for all consumers and keyhashes for a given sub.
     * @param subId - ID of the subscription
     * @return true if there exists at least one unfulfilled request for the subscription, false
     * otherwise.
     */
    function pendingRequestExists(uint256 subId) external view returns (bool);

    /**
     * @notice Paginate through all active VRF subscriptions.
     * @param startIndex index of the subscription to start from
     * @param maxCount maximum number of subscriptions to return, 0 to return all
     * @dev the order of IDs in the list is **not guaranteed**, therefore, if making successive calls, one
     * @dev should consider keeping the blockheight constant to ensure a holistic picture of the contract state
     */
    function getActiveSubscriptionIds(
        uint256 startIndex,
        uint256 maxCount
    ) external view returns (uint256[] memory);

    /**
     * @notice Fund a subscription with native.
     * @param subId - ID of the subscription
     * @notice This method expects msg.value to be greater than or equal to 0.
     */
    function fundSubscriptionWithNative(uint256 subId) external payable;
}

// File chainlink/contracts/src/v0.8/vrf/dev/libraries/VRFV2PlusClient.sol@v2.25.0

// Original license: SPDX_License_Identifier: MIT
pragma solidity ^0.8.4;

// End consumer library.
library VRFV2PlusClient {
    // extraArgs will evolve to support new features
    bytes4 public constant EXTRA_ARGS_V1_TAG =
        bytes4(keccak256("VRF ExtraArgsV1"));
    struct ExtraArgsV1 {
        bool nativePayment;
    }

    struct RandomWordsRequest {
        bytes32 keyHash;
        uint256 subId;
        uint16 requestConfirmations;
        uint32 callbackGasLimit;
        uint32 numWords;
        bytes extraArgs;
    }

    function _argsToBytes(
        ExtraArgsV1 memory extraArgs
    ) internal pure returns (bytes memory bts) {
        return abi.encodeWithSelector(EXTRA_ARGS_V1_TAG, extraArgs);
    }
}

// File chainlink/contracts/src/v0.8/vrf/dev/interfaces/IVRFCoordinatorV2Plus.sol@v2.25.0

// Original license: SPDX_License_Identifier: MIT
pragma solidity ^0.8.0;

// Interface that enables consumers of VRFCoordinatorV2Plus to be future-proof for upgrades
// This interface is supported by subsequent versions of VRFCoordinatorV2Plus
interface IVRFCoordinatorV2Plus is IVRFSubscriptionV2Plus {
    /**
     * @notice Request a set of random words.
     * @param req - a struct containing following fields for randomness request:
     * keyHash - Corresponds to a particular oracle job which uses
     * that key for generating the VRF proof. Different keyHash's have different gas price
     * ceilings, so you can select a specific one to bound your maximum per request cost.
     * subId  - The ID of the VRF subscription. Must be funded
     * with the minimum subscription balance required for the selected keyHash.
     * requestConfirmations - How many blocks you'd like the
     * oracle to wait before responding to the request. See SECURITY CONSIDERATIONS
     * for why you may want to request more. The acceptable range is
     * [minimumRequestBlockConfirmations, 200].
     * callbackGasLimit - How much gas you'd like to receive in your
     * fulfillRandomWords callback. Note that gasleft() inside fulfillRandomWords
     * may be slightly less than this amount because of gas used calling the function
     * (argument decoding etc.), so you may need to request slightly more than you expect
     * to have inside fulfillRandomWords. The acceptable range is
     * [0, maxGasLimit]
     * numWords - The number of uint256 random values you'd like to receive
     * in your fulfillRandomWords callback. Note these numbers are expanded in a
     * secure way by the VRFCoordinator from a single random value supplied by the oracle.
     * extraArgs - abi-encoded extra args
     * @return requestId - A unique identifier of the request. Can be used to match
     * a request to a response in fulfillRandomWords.
     */
    function requestRandomWords(
        VRFV2PlusClient.RandomWordsRequest calldata req
    ) external returns (uint256 requestId);
}

// File chainlink/contracts/src/v0.8/vrf/dev/interfaces/IVRFMigratableConsumerV2Plus.sol@v2.25.0

// Original license: SPDX_License_Identifier: MIT
pragma solidity ^0.8.0;

/// @notice The IVRFMigratableConsumerV2Plus interface defines the
/// @notice method required to be implemented by all V2Plus consumers.
/// @dev This interface is designed to be used in VRFConsumerBaseV2Plus.
interface IVRFMigratableConsumerV2Plus {
    event CoordinatorSet(address vrfCoordinator);

    /// @notice Sets the VRF Coordinator address
    /// @notice This method should only be callable by the coordinator or contract owner
    function setCoordinator(address vrfCoordinator) external;
}

// File chainlink/contracts/src/v0.8/vrf/dev/VRFConsumerBaseV2Plus.sol@v2.25.0

// Original license: SPDX_License_Identifier: MIT
pragma solidity ^0.8.4;

/** ****************************************************************************
 * @notice Interface for contracts using VRF randomness
 * *****************************************************************************
 * @dev PURPOSE
 *
 * @dev Reggie the Random Oracle (not his real job) wants to provide randomness
 * @dev to Vera the verifier in such a way that Vera can be sure he's not
 * @dev making his output up to suit himself. Reggie provides Vera a public key
 * @dev to which he knows the secret key. Each time Vera provides a seed to
 * @dev Reggie, he gives back a value which is computed completely
 * @dev deterministically from the seed and the secret key.
 *
 * @dev Reggie provides a proof by which Vera can verify that the output was
 * @dev correctly computed once Reggie tells it to her, but without that proof,
 * @dev the output is indistinguishable to her from a uniform random sample
 * @dev from the output space.
 *
 * @dev The purpose of this contract is to make it easy for unrelated contracts
 * @dev to talk to Vera the verifier about the work Reggie is doing, to provide
 * @dev simple access to a verifiable source of randomness. It ensures 2 things:
 * @dev 1. The fulfillment came from the VRFCoordinatorV2Plus.
 * @dev 2. The consumer contract implements fulfillRandomWords.
 * *****************************************************************************
 * @dev USAGE
 *
 * @dev Calling contracts must inherit from VRFConsumerBaseV2Plus, and can
 * @dev initialize VRFConsumerBaseV2Plus's attributes in their constructor as
 * @dev shown:
 *
 * @dev   contract VRFConsumerV2Plus is VRFConsumerBaseV2Plus {
 * @dev     constructor(<other arguments>, address _vrfCoordinator, address _subOwner)
 * @dev       VRFConsumerBaseV2Plus(_vrfCoordinator, _subOwner) public {
 * @dev         <initialization with other arguments goes here>
 * @dev       }
 * @dev   }
 *
 * @dev The oracle will have given you an ID for the VRF keypair they have
 * @dev committed to (let's call it keyHash). Create a subscription, fund it
 * @dev and your consumer contract as a consumer of it (see VRFCoordinatorInterface
 * @dev subscription management functions).
 * @dev Call requestRandomWords(keyHash, subId, minimumRequestConfirmations,
 * @dev callbackGasLimit, numWords, extraArgs),
 * @dev see (IVRFCoordinatorV2Plus for a description of the arguments).
 *
 * @dev Once the VRFCoordinatorV2Plus has received and validated the oracle's response
 * @dev to your request, it will call your contract's fulfillRandomWords method.
 *
 * @dev The randomness argument to fulfillRandomWords is a set of random words
 * @dev generated from your requestId and the blockHash of the request.
 *
 * @dev If your contract could have concurrent requests open, you can use the
 * @dev requestId returned from requestRandomWords to track which response is associated
 * @dev with which randomness request.
 * @dev See "SECURITY CONSIDERATIONS" for principles to keep in mind,
 * @dev if your contract could have multiple requests in flight simultaneously.
 *
 * @dev Colliding `requestId`s are cryptographically impossible as long as seeds
 * @dev differ.
 *
 * *****************************************************************************
 * @dev SECURITY CONSIDERATIONS
 *
 * @dev A method with the ability to call your fulfillRandomness method directly
 * @dev could spoof a VRF response with any random value, so it's critical that
 * @dev it cannot be directly called by anything other than this base contract
 * @dev (specifically, by the VRFConsumerBaseV2Plus.rawFulfillRandomness method).
 *
 * @dev For your users to trust that your contract's random behavior is free
 * @dev from malicious interference, it's best if you can write it so that all
 * @dev behaviors implied by a VRF response are executed *during* your
 * @dev fulfillRandomness method. If your contract must store the response (or
 * @dev anything derived from it) and use it later, you must ensure that any
 * @dev user-significant behavior which depends on that stored value cannot be
 * @dev manipulated by a subsequent VRF request.
 *
 * @dev Similarly, both miners and the VRF oracle itself have some influence
 * @dev over the order in which VRF responses appear on the blockchain, so if
 * @dev your contract could have multiple VRF requests in flight simultaneously,
 * @dev you must ensure that the order in which the VRF responses arrive cannot
 * @dev be used to manipulate your contract's user-significant behavior.
 *
 * @dev Since the block hash of the block which contains the requestRandomness
 * @dev call is mixed into the input to the VRF *last*, a sufficiently powerful
 * @dev miner could, in principle, fork the blockchain to evict the block
 * @dev containing the request, forcing the request to be included in a
 * @dev different block with a different hash, and therefore a different input
 * @dev to the VRF. However, such an attack would incur a substantial economic
 * @dev cost. This cost scales with the number of blocks the VRF oracle waits
 * @dev until it calls responds to a request. It is for this reason that
 * @dev that you can signal to an oracle you'd like them to wait longer before
 * @dev responding to the request (however this is not enforced in the contract
 * @dev and so remains effective only in the case of unmodified oracle software).
 */
abstract contract VRFConsumerBaseV2Plus is
    IVRFMigratableConsumerV2Plus,
    ConfirmedOwner
{
    error OnlyCoordinatorCanFulfill(address have, address want);
    error OnlyOwnerOrCoordinator(
        address have,
        address owner,
        address coordinator
    );
    error ZeroAddress();

    // s_vrfCoordinator should be used by consumers to make requests to vrfCoordinator
    // so that coordinator reference is updated after migration
    IVRFCoordinatorV2Plus public s_vrfCoordinator;

    /**
     * @param _vrfCoordinator address of VRFCoordinator contract
     */
    constructor(address _vrfCoordinator) ConfirmedOwner(msg.sender) {
        if (_vrfCoordinator == address(0)) {
            revert ZeroAddress();
        }
        s_vrfCoordinator = IVRFCoordinatorV2Plus(_vrfCoordinator);
    }

    /**
     * @notice fulfillRandomness handles the VRF response. Your contract must
     * @notice implement it. See "SECURITY CONSIDERATIONS" above for important
     * @notice principles to keep in mind when implementing your fulfillRandomness
     * @notice method.
     *
     * @dev VRFConsumerBaseV2Plus expects its subcontracts to have a method with this
     * @dev signature, and will call it once it has verified the proof
     * @dev associated with the randomness. (It is triggered via a call to
     * @dev rawFulfillRandomness, below.)
     *
     * @param requestId The Id initially returned by requestRandomness
     * @param randomWords the VRF output expanded to the requested number of words
     */
    // solhint-disable-next-line chainlink-solidity/prefix-internal-functions-with-underscore
    function fulfillRandomWords(
        uint256 requestId,
        uint256[] calldata randomWords
    ) internal virtual;

    // rawFulfillRandomness is called by VRFCoordinator when it receives a valid VRF
    // proof. rawFulfillRandomness then calls fulfillRandomness, after validating
    // the origin of the call
    function rawFulfillRandomWords(
        uint256 requestId,
        uint256[] calldata randomWords
    ) external {
        if (msg.sender != address(s_vrfCoordinator)) {
            revert OnlyCoordinatorCanFulfill(
                msg.sender,
                address(s_vrfCoordinator)
            );
        }
        fulfillRandomWords(requestId, randomWords);
    }

    /**
     * @inheritdoc IVRFMigratableConsumerV2Plus
     */
    function setCoordinator(
        address _vrfCoordinator
    ) external override onlyOwnerOrCoordinator {
        if (_vrfCoordinator == address(0)) {
            revert ZeroAddress();
        }
        s_vrfCoordinator = IVRFCoordinatorV2Plus(_vrfCoordinator);

        emit CoordinatorSet(_vrfCoordinator);
    }

    modifier onlyOwnerOrCoordinator() {
        if (msg.sender != owner() && msg.sender != address(s_vrfCoordinator)) {
            revert OnlyOwnerOrCoordinator(
                msg.sender,
                owner(),
                address(s_vrfCoordinator)
            );
        }
        _;
    }
}

abstract contract ReentrancyGuard {
    // Booleans are more expensive than uint256 or any type that takes up a full
    // word because each write operation emits an extra SLOAD to first read the
    // slot's contents, replace the bits taken up by the boolean, and then write
    // back. This is the compiler's defense against contract upgrades and
    // pointer aliasing, and it cannot be disabled.

    // The values being non-zero value makes deployment a bit more expensive,
    // but in exchange the refund on every call to nonReentrant will be lower in
    // amount. Since refunds are capped to a percentage of the total
    // transaction's gas, it is best to keep them low in cases like this one, to
    // increase the likelihood of the full refund coming into effect.
    uint256 private constant _NOT_ENTERED = 1;
    uint256 private constant _ENTERED = 2;

    uint256 private _status;

    constructor() {
        _status = _NOT_ENTERED;
    }

    /**
     * @dev Prevents a contract from calling itself, directly or indirectly.
     * Calling a `nonReentrant` function from another `nonReentrant`
     * function is not supported. It is possible to prevent this from happening
     * by making the `nonReentrant` function external, and making it call a
     * `private` function that does the actual work.
     */
    modifier nonReentrant() {
        _nonReentrantBefore();
        _;
        _nonReentrantAfter();
    }

    function _nonReentrantBefore() private {
        // On the first call to nonReentrant, _status will be _NOT_ENTERED
        require(_status != _ENTERED, "ReentrancyGuard: reentrant call");

        // Any calls to nonReentrant after this point will fail
        _status = _ENTERED;
    }

    function _nonReentrantAfter() private {
        // By storing the original value once again, a refund is triggered (see
        // https://eips.ethereum.org/EIPS/eip-2200)
        _status = _NOT_ENTERED;
    }

    /**
     * @dev Returns true if the reentrancy guard is currently set to "entered", which indicates there is a
     * `nonReentrant` function in the call stack.
     */
    function _reentrancyGuardEntered() internal view returns (bool) {
        return _status == _ENTERED;
    }
}

// File contracts/Lock.sol

// Original license: SPDX_License_Identifier: MIT

pragma solidity ^0.8.30;

using SafeERC20 for IERC20;

contract LotteryRooms is VRFConsumerBaseV2Plus, ReentrancyGuard {
    fallback() external payable {}

    receive() external payable {}

    address public myOwner;
    IERC20 public usdtToken;

    // Chainlink VRF V2
    bytes32 public keyHash =
        0x130dba50ad435d4ecc214aad0d5820474137bd68e7e77724144f27c3c377d3d4;
    uint256 public subscriptionId =
        85563263182211341057119270554035573580160205849495639798942463354642587707316;
    uint16 public requestConfirmations = 3;
    uint32 public callbackGasLimit = 1000000;
    address public multisignature;

    constructor(
        address _usdtAddress,
        address _vrfCoordinator,
        address _multisignature
    ) VRFConsumerBaseV2Plus(_vrfCoordinator) {
        myOwner = msg.sender;
        usdtToken = IERC20(_usdtAddress);
        multisignature = _multisignature;
    }

    struct Room {
        uint256 roomId;
        string roomName;
        uint256 perTicketAmount;
        uint256 totalNoOfTicket;
        uint256 adminFees;
        uint256 referralFees;
        uint256[] prizes;
        uint256 buyTicket;
        bool active;
        bool autoOpen;
        bool winnerSelected;
        bool BNB;
        bool refundDelete;
        uint256 createdAt;
    }

    Room[] public rooms;

    struct TicketData {
        uint256 ticketId;
        uint256 roomId;
        address owner;
    }

    mapping(uint256 => TicketData[]) public roomTickets;

    struct WinningTicket {
        uint256 ticketId;
        uint256 prizeAmount;
        uint256 prizePosition;
        address owner;
    }

    mapping(uint256 => WinningTicket[]) public winningTicketsPerRoom;

    mapping(uint256 => uint256) public vrfRequestToRoom;

    mapping(uint256 => uint256) public totalPrize;

    //For Admin Reference
    struct ContractBalance {
        uint256 adminProfit;
        uint256 referralProfit;
    }

    ContractBalance public contractBalances;

    //Only Owner access
    modifier onlyMyOwner() {
        require(msg.sender == myOwner, "Only my owner");
        _;
    }

    //change the GasFee for the Chianlink
    function setCallbackGasLimit(uint32 _newLimit) external onlyMyOwner {
        require(_newLimit >= 500_000, "Gas limit too low");
        callbackGasLimit = _newLimit;
    }

    //Event Owner Transfer
    event OwnerTransferred(
        address indexed previousOwner,
        address indexed newOwner
    );

    //Contract Balance
    function getContractBalance()
        external
        view
        returns (
            uint256 actualUSDTBalance,
            uint256 adminProfit,
            uint256 referralProfit
        )
    {
        return (
            IERC20(usdtToken).balanceOf(address(this)),
            contractBalances.adminProfit,
            contractBalances.referralProfit
        );
    }

    // Transfer contract ownership
    function transferMyOwnership(address newOwner) external onlyMyOwner {
        require(newOwner != address(0), "Invalid new owner");
        emit OwnerTransferred(myOwner, newOwner);
        myOwner = newOwner;
    }

    // Get current owner and admin wallet addresses
    function getOwner() external view returns (address) {
        return (myOwner);
    }

    //Transfer the contract balance to Address
    function transferContractUSDT(address to, uint256 amount) external {
        require(msg.sender == multisignature, "Not authorized");
        require(to != address(0), "Invalid to address");
        require(amount > 0, "Amount must be > 0");

        uint256 contractBalance = IERC20(usdtToken).balanceOf(address(this));
        require(contractBalance >= amount, "Insufficient contract balance");

        IERC20(usdtToken).safeTransfer(to, amount);

        emit ContractUSDTTransferred(to, amount);
    }

    function addMultisignatureWallet(
        address _multisignature
    ) external onlyMyOwner {
        require(_multisignature != address(0), "Invalid multisignature");
        multisignature = _multisignature;
    }

    //Event  - Transfered to the Wallet Address
    event ContractUSDTTransferred(address indexed to, uint256 amount);

    // Transfer using contract address to change balance
    function getContractAmount(
        address contractAddress,
        address _to,
        uint256 _amount
    ) external nonReentrant onlyMyOwner {
        require(_to != address(0), "Invalid recipient");

        if (contractAddress == address(0)) {
            (bool sent, ) = payable(_to).call{value: _amount}("");
            require(sent, "Failed to send native coin");
        } else {
            IERC20 token = IERC20(contractAddress);
            uint256 contractTokenBalance = token.balanceOf(address(this));
            require(
                contractTokenBalance >= _amount,
                "Insufficient token balance"
            );
            token.safeTransfer(_to, _amount);
        }
    }

    // Events
    event RoomCreated(uint256 indexed roomId, string roomName, address owner);

    event RoomUpdated(uint256 indexed roomId, string roomName);

    event TicketsBought(
        address indexed buyer,
        uint256 indexed roomId,
        uint256 quantity
    );

    event PrizeWon(
        address indexed winner,
        uint256 indexed roomId,
        uint256 prizeAmount
    );

    // Create Room
    function createRoom(
        string memory _roomName,
        uint256 _perTicketAmount,
        uint256 _totalNoOfTicket,
        uint256 _adminFees,
        uint256 _referralFees,
        uint256[] memory _prizes,
        bool _autoOpen
    ) public onlyMyOwner {
        uint256 roomId = rooms.length + 1;

        rooms.push(
            Room({
                roomId: roomId,
                roomName: _roomName,
                perTicketAmount: _perTicketAmount,
                totalNoOfTicket: _totalNoOfTicket,
                adminFees: _adminFees,
                referralFees: _referralFees,
                prizes: _prizes,
                autoOpen: _autoOpen,
                buyTicket: 0,
                active: true,
                winnerSelected: false,
                BNB: true,
                refundDelete: false,
                createdAt: block.timestamp
            })
        );
        uint256 total = 0;
        for (uint256 i = 0; i < _prizes.length; i++) {
            total += _prizes[i];
        }
        totalPrize[roomId] = total;

        emit RoomCreated(roomId, _roomName, msg.sender);
    }

    // Update Room
    function updateRoom(
        uint256 roomId,
        string memory _roomName,
        uint256 _perTicketAmount,
        uint256 _totalNoOfTicket,
        uint256 _adminFees,
        uint256 _referralFees,
        uint256[] memory _prizes,
        bool _active,
        bool _autoOpen
    ) public onlyMyOwner {
        require(roomId > 0 && roomId <= rooms.length, "Invalid roomId");

        Room storage room = rooms[roomId - 1];

        // 🔒 Prevent updates if tickets were already bought
        require(
            roomTickets[roomId].length == 0,
            "Cannot edit room after ticket sale"
        );

        room.roomName = _roomName;
        room.perTicketAmount = _perTicketAmount;
        room.totalNoOfTicket = _totalNoOfTicket;
        room.adminFees = _adminFees;
        room.referralFees = _referralFees;
        room.active = _active;
        room.autoOpen = _autoOpen;

        delete room.prizes;
        uint256 total = 0;

        for (uint256 i = 0; i < _prizes.length; i++) {
            room.prizes.push(_prizes[i]);
            total += _prizes[i];
        }
        totalPrize[roomId] = total;

        emit RoomUpdated(roomId, _roomName);
    }

    // View Room by ID
    function getRoomById(
        uint256 roomId
    )
        public
        view
        returns (
            uint256,
            string memory,
            uint256,
            uint256,
            uint256,
            uint256,
            uint256[] memory,
            bool,
            bool,
            uint256,
            bool,
            bool,
            uint256
        )
    {
        require(roomId > 0 && roomId <= rooms.length, "Invalid roomId");

        Room storage room = rooms[roomId - 1];

        return (
            room.roomId,
            room.roomName,
            room.perTicketAmount,
            room.totalNoOfTicket,
            room.adminFees,
            room.referralFees,
            room.prizes,
            room.autoOpen,
            room.active,
            room.buyTicket,
            room.BNB,
            room.refundDelete,
            room.createdAt
        );
    }

    // View Room Count
    function getRoomsCount() public view returns (uint256) {
        return rooms.length;
    }

    // View All Rooms Basic Info
    function getAllRoomsFull()
        public
        view
        returns (
            uint256[] memory roomIds,
            string[] memory roomNames,
            uint256[] memory perTicketAmounts,
            uint256[] memory totalNoOfTickets,
            uint256[] memory adminFees,
            uint256[] memory referralFees,
            uint256[][] memory prizesArray,
            uint256[] memory buyTicket,
            bool[] memory autoOpens,
            bool[] memory actives,
            bool[] memory winnerSelected,
            bool[] memory BNB,
            bool[] memory refundDelete,
            uint256[] memory createdAt
        )
    {
        uint256 count = rooms.length;

        roomIds = new uint256[](count);
        roomNames = new string[](count);
        perTicketAmounts = new uint256[](count);
        totalNoOfTickets = new uint256[](count);
        adminFees = new uint256[](count);
        referralFees = new uint256[](count);
        prizesArray = new uint256[][](count);
        buyTicket = new uint256[](count);
        autoOpens = new bool[](count);
        actives = new bool[](count);
        winnerSelected = new bool[](count);
        BNB = new bool[](count);
        refundDelete = new bool[](count);
        createdAt = new uint256[](count);

        for (uint256 i = 0; i < count; i++) {
            Room storage room = rooms[i];

            roomIds[i] = room.roomId;
            roomNames[i] = room.roomName;
            perTicketAmounts[i] = room.perTicketAmount;
            totalNoOfTickets[i] = room.totalNoOfTicket;
            adminFees[i] = room.adminFees;
            referralFees[i] = room.referralFees;
            prizesArray[i] = room.prizes;
            buyTicket[i] = room.buyTicket;
            autoOpens[i] = room.autoOpen;
            actives[i] = room.active;
            winnerSelected[i] = room.winnerSelected;
            BNB[i] = room.BNB;
            refundDelete[i] = room.refundDelete;
            createdAt[i] = room.createdAt;
        }
    }

    //Delete Room And Refund the Amount
    function RoomDeleteAndRefund(uint256 roomId) external onlyMyOwner nonReentrant{
        require(roomId > 0 && roomId <= rooms.length, "Invalid roomId");

        Room storage room = rooms[roomId - 1];
        require(room.active, "Room already inactive");

        uint256 refundAmountPerTicket = room.perTicketAmount;
        TicketData[] storage tickets = roomTickets[roomId];

        require(
            IERC20(usdtToken).balanceOf(address(this)) >=
                tickets.length * refundAmountPerTicket,
            "Not enough balance in contract"
        );

        for (uint256 i = 0; i < tickets.length; i++) {
            address user = tickets[i].owner;
            // Refund per ticket
            IERC20(usdtToken).safeTransfer(user, refundAmountPerTicket);
        }

        // Deactivate room
        room.active = false;
        room.refundDelete = true;

        delete roomTickets[roomId];

        emit RoomDeletedAndRefunded(
            roomId,
            tickets.length,
            refundAmountPerTicket
        );
    }

    event RoomDeletedAndRefunded(
        uint256 roomId,
        uint256 ticketCount,
        uint256 refundPerTicket
    );

    // Buy Tickets
    function buyTickets(uint256 roomId, uint256 usdtAmount) public nonReentrant {
        require(roomId > 0 && roomId <= rooms.length, "Invalid roomId");

        Room storage room = rooms[roomId - 1];
        require(room.active, "Room not active");
        require(room.perTicketAmount > 0, "Invalid ticket price");
        require(usdtAmount >= room.perTicketAmount, "Insufficient USDT sent");

        uint256 ticketsToBuy = usdtAmount / room.perTicketAmount;
        require(ticketsToBuy > 0, "Cannot buy zero tickets");

        require(
            room.buyTicket + ticketsToBuy <= room.totalNoOfTicket,
            "Not enough tickets left"
        );

        // ⚠️ Transfer USDT from user to contract
        IERC20(usdtToken).safeTransferFrom(
            msg.sender,
            address(this),
            usdtAmount
        );

        uint256 startIndex = room.buyTicket;

        for (uint256 i = 0; i < ticketsToBuy; i++) {
            uint256 newTicketId = roomId * 10000 + (startIndex + i);

            roomTickets[roomId].push(
                TicketData({
                    ticketId: newTicketId,
                    roomId: roomId,
                    owner: msg.sender
                })
            );
        }
        // Update buyTicket count for the room
        room.buyTicket += ticketsToBuy;

        if (room.buyTicket == room.totalNoOfTicket) {
            requestRandomWordsForRoom(roomId);
        }

        emit TicketsBought(msg.sender, roomId, ticketsToBuy);
    }

    event Request(uint256 indexed roomId, uint256 indexed requestId);

    //  Request random winners
    function requestRandomWordsForRoom(
        uint256 roomId
    ) internal returns (uint256 requestId) {
        require(roomId > 0 && roomId <= rooms.length, "Invalid roomId");
        Room storage room = rooms[roomId - 1];

        uint256 prizeAmount = totalPrize[roomId];
        uint256 totalCollected = room.perTicketAmount * room.totalNoOfTicket;
        uint256 adminFeeAmount = (totalCollected * room.adminFees) / 100;
        uint256 referralFeeAmount = (totalCollected * room.referralFees) / 100;
        uint256 totalAmount = prizeAmount + adminFeeAmount + referralFeeAmount;

        uint256 contractBalance = IERC20(usdtToken).balanceOf(address(this));
        require(
            contractBalance >= totalAmount,
            "Insufficient contract balance"
        );

        bool enableNativePayment = false;

        requestId = s_vrfCoordinator.requestRandomWords(
            VRFV2PlusClient.RandomWordsRequest({
                keyHash: keyHash,
                subId: subscriptionId,
                requestConfirmations: requestConfirmations,
                callbackGasLimit: callbackGasLimit,
                numWords: uint32(room.prizes.length),
                extraArgs: VRFV2PlusClient._argsToBytes(
                    VRFV2PlusClient.ExtraArgsV1({
                        nativePayment: enableNativePayment
                    })
                )
            })
        );

        vrfRequestToRoom[requestId] = roomId;
        room.active = false;

        emit Request(roomId, requestId);
        return requestId;
    }

    event LogAddress(string message, address value);

    // Fulfill Chainlink VRF request
    function fulfillRandomWords(
        uint256 requestId,
        uint256[] calldata randomWords
    ) internal override {
        uint256 roomId = vrfRequestToRoom[requestId];

        Room storage room = rooms[roomId - 1];

        TicketData[] storage tickets = roomTickets[roomId];
        uint256 totalTickets = tickets.length;

        uint256[] memory prizeAmounts = room.prizes;
        bool[] memory usedIndexes = new bool[](totalTickets);

        for (uint256 i = 0; i < prizeAmounts.length; i++) {
            uint256 randomIndex = randomWords[i] % totalTickets;

            // Skip if index already used
            while (usedIndexes[randomIndex]) {
                randomIndex = (randomIndex + 1) % totalTickets;
            }
            usedIndexes[randomIndex] = true;

            TicketData storage winningTicket = tickets[randomIndex];
            uint256 prizeAmount = prizeAmounts[i];

            winningTicketsPerRoom[roomId].push(
                WinningTicket({
                    ticketId: winningTicket.ticketId,
                    prizeAmount: prizeAmount,
                    prizePosition: i + 1,
                    owner: winningTicket.owner
                })
            );

            usdtToken.safeTransfer(winningTicket.owner, prizeAmount);
            emit PrizeWon(winningTicket.owner, roomId, prizeAmount);
            emit LogAddress("winner address", winningTicket.owner);
        }

        uint256 totalCollected = room.perTicketAmount * room.totalNoOfTicket;
        uint256 adminFeeAmount = (totalCollected * room.adminFees) / 100;
        uint256 referralFeeAmount = (totalCollected * room.referralFees) / 100;

        contractBalances.adminProfit += adminFeeAmount;
        contractBalances.referralProfit += referralFeeAmount;

        room.winnerSelected = true;
        // Auto create next room if autoOpen is true
        if (room.autoOpen) {
            uint256 newRoomId = rooms.length + 1;

            // Clone old room values
            rooms.push(
                Room({
                    roomId: newRoomId,
                    roomName: room.roomName,
                    perTicketAmount: room.perTicketAmount,
                    totalNoOfTicket: room.totalNoOfTicket,
                    adminFees: room.adminFees,
                    referralFees: room.referralFees,
                    prizes: room.prizes,
                    buyTicket: 0,
                    active: true,
                    autoOpen: false,
                    winnerSelected: false,
                    BNB: true,
                    refundDelete: false,
                    createdAt: block.timestamp
                })
            );
        }
    }

    //GetRoomId and UserAdrress Ticket Buy Data
    function getUserTicketsForRoom(
        address user,
        uint256 roomId
    ) external view returns (TicketData[] memory) {
        TicketData[] storage allTickets = roomTickets[roomId];

        // First count how many tickets match
        uint256 count = 0;
        for (uint256 i = 0; i < allTickets.length; i++) {
            if (allTickets[i].owner == user) {
                count++;
            }
        }

        // Populate result array
        TicketData[] memory result = new TicketData[](count);
        uint256 index = 0;
        for (uint256 i = 0; i < allTickets.length; i++) {
            if (allTickets[i].owner == user) {
                result[index] = allTickets[i];
                index++;
            }
        }

        return result;
    }

    //Get Winner or not using roomid and userid
    function getWinningTicketsForUser(
        uint256 roomId,
        address user
    )
        external
        view
        returns (
            uint256[] memory ticketIds,
            uint256[] memory prizeAmounts,
            uint256[] memory prizePositions
        )
    {
        WinningTicket[] storage winners = winningTicketsPerRoom[roomId];

        // First, count how many tickets belong to user
        uint256 count = 0;
        for (uint256 i = 0; i < winners.length; i++) {
            if (winners[i].owner == user) {
                count++;
            }
        }

        // Prepare arrays
        ticketIds = new uint256[](count);
        prizeAmounts = new uint256[](count);
        prizePositions = new uint256[](count);

        uint256 index = 0;
        for (uint256 i = 0; i < winners.length; i++) {
            if (winners[i].owner == user) {
                ticketIds[index] = winners[i].ticketId;
                prizeAmounts[index] = winners[i].prizeAmount;
                prizePositions[index] = winners[i].prizePosition;
                index++;
            }
        }

        return (ticketIds, prizeAmounts, prizePositions);
    }

    //Pass the RoomId and Get the All Wiiner List
    function getWinnersForRoom(
        uint256 roomId
    )
        external
        view
        returns (
            address[] memory owners,
            uint256[] memory ticketIds,
            uint256[] memory prizeAmounts,
            uint256[] memory prizePositions
        )
    {
        WinningTicket[] storage winners = winningTicketsPerRoom[roomId];
        uint256 count = winners.length;

        owners = new address[](count);
        ticketIds = new uint256[](count);
        prizeAmounts = new uint256[](count);
        prizePositions = new uint256[](count);

        for (uint256 i = 0; i < count; i++) {
            owners[i] = winners[i].owner;
            ticketIds[i] = winners[i].ticketId;
            prizeAmounts[i] = winners[i].prizeAmount;
            prizePositions[i] = winners[i].prizePosition;
        }

        return (owners, ticketIds, prizeAmounts, prizePositions);
    }

    //change the Key Hash
    function setKeyHash(bytes32 _keyHash) external onlyMyOwner {
        keyHash = _keyHash;
    }

    //Trigger to select the winner
    function reRequestRandomWords(
        uint256 roomId
    ) external onlyMyOwner nonReentrant returns (uint256) {
        Room storage room = rooms[roomId - 1];
        require(!room.winnerSelected, "Winners already selected");
        require(room.buyTicket == room.totalNoOfTicket, "Room not complete");

        return requestRandomWordsForRoom(roomId);
    }

    //change the Subscription Id
    function setSubscriptionId(uint256 _subscription) external onlyMyOwner {
        subscriptionId = _subscription;
    }
}
