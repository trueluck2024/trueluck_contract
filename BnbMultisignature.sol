/**
 *Submitted for verification at BscScan.com on 2025-09-04
*/

/**
 *Submitted for verification at polygonscan.com on 2025-07-09
*/

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

interface LotteryRooms {
    function transferContractUSDT(address to, uint256 amount) external;
}

contract Multisignature {
    address[] public owners;
    uint256 public required;
    address public creator;

    struct Transaction {
        address to;
        uint256 value;
        bool executed;
        uint256 confirmations;
        address lotterycontract;
    }

    Transaction[] public transactions;
    mapping(uint256 => mapping(address => bool)) public isConfirmed;

    modifier onlyOwner() {
        bool ownerExists = false;
        for (uint256 i = 0; i < owners.length; i++) {
            if (owners[i] == msg.sender) {
                ownerExists = true;
                break;
            }
        }
        require(ownerExists, "Not an owner");
        _;
    }

    constructor(address[] memory _owners,address _creator, uint256 _required) {
        require(_owners.length >= _required, "Invalid config");
        owners = _owners;
        required = _required;
        creator = _creator;
    }


    function creatorChange(address _creator) external  { 
        require(msg.sender != creator, "Creator cannot be removed");
        creator = _creator;
    }


    //Get All the Owner List
    function getOwners() external view returns (address[] memory) {
        return owners;
    }

    //Add aditional or Reduced signature required
    function addSignatureRequired(uint256 _value) external onlyOwner {
        required = _value;
    }

    //Create a signature data for new transaction
    function submitTransaction(
        address _lotteryContract,
        address _to,
        uint256 _value
    ) external onlyOwner {
        uint256 txIndex = transactions.length;
        transactions.push(
            Transaction({
                to: _to,
                value: _value,
                executed: false,
                confirmations: 0,
                lotterycontract: _lotteryContract
            })
        );

        emit TransactionSubmitted(txIndex, _to, _value, _lotteryContract);
    }

    event TransactionSubmitted(
        uint256 indexed txIndex,
        address indexed to,
        uint256 value,
        address indexed lotteryContract
    );

    // Confirm the transaction by the calling wallet (must be an owner).
    // If enough confirmations are collected, execute the transaction.
    function confirmTransaction(
        address to,
        uint256 amount,
        uint256 _txIndex
    ) external onlyOwner {
        Transaction storage txObj = transactions[_txIndex];
        require(!txObj.executed, "Already executed");
        require(!isConfirmed[_txIndex][msg.sender], "Already confirmed");

        isConfirmed[_txIndex][msg.sender] = true;
        txObj.confirmations += 1;

        if (txObj.confirmations >= required) {
            executeTransaction(to, amount, _txIndex);
        }
    }

    // Execute the transaction if enough confirmations are collected.
    function executeTransaction(
        address to,
        uint256 amount,
        uint256 _txIndex
    ) internal {
        Transaction storage txObj = transactions[_txIndex];
        require(!txObj.executed, "Already executed");
        LotteryRooms(txObj.lotterycontract).transferContractUSDT(to, amount);
        txObj.executed = true;
    }

    //Get Transaction Approve List
    function getApprovers(uint256 _txIndex)
        external
        view
        returns (address[] memory)
    {
        address[] memory approversTemp = new address[](owners.length);
        uint256 count = 0;

        for (uint256 i = 0; i < owners.length; i++) {
            if (isConfirmed[_txIndex][owners[i]]) {
                approversTemp[count] = owners[i];
                count++;
            }
        }

        // Resize array to actual count
        address[] memory approvers = new address[](count);
        for (uint256 i = 0; i < count; i++) {
            approvers[i] = approversTemp[i];
        }

        return approvers;
    }

    function revokeConfirmation(uint256 _txIndex) external onlyOwner {
        Transaction storage txObj = transactions[_txIndex];

        require(!txObj.executed, "Transaction already executed");
        require(isConfirmed[_txIndex][msg.sender], "Transaction not confirmed");

        isConfirmed[_txIndex][msg.sender] = false;
        txObj.confirmations -= 1;
    }

    function addOwner(address _newOwner) external onlyOwner {
        require(_newOwner != address(0), "Invalid address");
        require(!isOwner(_newOwner), "Already an owner");

        owners.push(_newOwner);
    }

    function isOwner(address _addr) public view returns (bool) {
        for (uint256 i = 0; i < owners.length; i++) {
            if (owners[i] == _addr) {
                return true;
            }
        }
        return false;
    }

    function removeOwner(address _ownerToRemove) external onlyOwner {
        require(isOwner(_ownerToRemove), "Not an owner");
        require(_ownerToRemove != creator, "Creator cannot be removed");

        require(
            owners.length - 1 >= required,
            "Can't remove, would break quorum"
        );

        // Remove from array
        for (uint256 i = 0; i < owners.length; i++) {
            if (owners[i] == _ownerToRemove) {
                owners[i] = owners[owners.length - 1]; // move last to removed slot
                owners.pop();
                break;
            }
        }

        // Optional: Clean up confirmations
        for (uint256 i = 0; i < transactions.length; i++) {
            if (isConfirmed[i][_ownerToRemove]) {
                isConfirmed[i][_ownerToRemove] = false;
                if (transactions[i].confirmations > 0) {
                    transactions[i].confirmations -= 1;
                }
            }
        }
    }
}
