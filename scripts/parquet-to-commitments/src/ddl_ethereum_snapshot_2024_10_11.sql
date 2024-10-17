-- v1.20 changes:
-- ERC1155_OWNERS table is now partitioned

CREATE SCHEMA IF NOT EXISTS ETHEREUM;

CREATE SCHEMA IF NOT EXISTS UNISWAP_V2_ETHEREUM;

CREATE SCHEMA IF NOT EXISTS UNISWAP_V3_ETHEREUM;

CREATE SCHEMA IF NOT EXISTS AAVE_V2_ETHEREUM;

CREATE SCHEMA IF NOT EXISTS AAVE_V3_ETHEREUM;

CREATE SCHEMA IF NOT EXISTS COMPOUND_V2_ETHEREUM;

CREATE SCHEMA IF NOT EXISTS COMPOUND_V3_ETHEREUM;

CREATE SCHEMA IF NOT EXISTS SPARK_ETHEREUM;

CREATE TABLE IF NOT EXISTS ETHEREUM.BLOCKS(
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP,
  BLOCK_HASH VARCHAR,
  MINER VARCHAR,
  REWARD DECIMAL(78, 0),
  SIZE_ INT,
  GAS_USED INT,
  GAS_LIMIT INT,
  BASE_FEE_PER_GAS DECIMAL(78, 0),
  TRANSACTION_COUNT INT,
  PARENT_HASH VARCHAR,
  PRIMARY KEY(BLOCK_NUMBER)
);

CREATE TABLE IF NOT EXISTS ETHEREUM.BLOCK_DETAILS(
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP,
  SHA3_UNCLES VARCHAR,
  STATE_ROOT VARCHAR,
  TRANSACTIONS_ROOT VARCHAR,
  RECEIPTS_ROOT VARCHAR,
  UNCLES_COUNT INT,
  VERSION VARCHAR,
  LOGS_BLOOM VARCHAR,
  NONCE VARCHAR,
  PRIMARY KEY(BLOCK_NUMBER)
);

CREATE TABLE IF NOT EXISTS ETHEREUM.TRANSACTIONS(
  TRANSACTION_HASH VARCHAR NOT NULL,
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP,
  TRANSACTION_FEE DECIMAL(78, 0),
  FROM_ADDRESS VARCHAR,
  TO_ADDRESS VARCHAR,
  VALUE_ DECIMAL(78, 0),
  GAS DECIMAL(78, 0),
  RECEIPT_CUMULATIVE_GAS_USED INT,
  RECEIPT_STATUS INT,
  PRIMARY KEY(BLOCK_NUMBER, TRANSACTION_HASH)
);

CREATE TABLE IF NOT EXISTS ETHEREUM.TRANSACTION_DETAILS(
  TRANSACTION_HASH VARCHAR NOT NULL,
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP NOT NULL,
  CHAIN_ID VARCHAR,
  FUNCTION_NAME VARCHAR,
  METHOD_ID VARCHAR,
  TRANSACTION_INDEX INT,
  RECEIPT_CONTRACT_ADDRESS VARCHAR,
  TYPE_ VARCHAR,
  GAS_PRICE DECIMAL(78, 0),
  NONCE INT,
  RECEIPT_GAS_USED INT,
  MAX_FEE_PER_GAS DECIMAL(78, 0),
  MAX_PRIORITY_FEE_PER_GAS DECIMAL(78, 0),
  RECEIPT_EFFECTIVE_GAS_PRICE DECIMAL(78, 0),
  LOGS_COUNT INT,
  PRIMARY KEY(BLOCK_NUMBER, TRANSACTION_HASH)
);

CREATE TABLE IF NOT EXISTS ETHEREUM.LOGS(
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP,
  TRANSACTION_HASH VARCHAR NOT NULL,
  EVENT_INDEX INT NOT NULL,
  NAME VARCHAR,
  CONTRACT_ADDRESS VARCHAR,
  TOPIC_0 VARCHAR,
  TOPIC_1 VARCHAR,
  TOPIC_2 VARCHAR,
  TOPIC_3 VARCHAR,
  STATUS INT,
  DATA_ VARCHAR,
  RAW_DATA VARCHAR,
  ANONYMOUS BOOLEAN,
  PRIMARY KEY(BLOCK_NUMBER, TRANSACTION_HASH, EVENT_INDEX)
);

CREATE TABLE IF NOT EXISTS ETHEREUM.CONTRACTS(
  CONTRACT_ADDRESS VARCHAR NOT NULL,
  TIME_STAMP TIMESTAMP,
  CONTRACT_CREATOR_ADDRESS VARCHAR,
  PROXY_CONTRACT_IMPL_ADDRESS VARCHAR,
  BLOCK_NUMBER BIGINT,
  TRANSACTION_HASH VARCHAR,
  PRIMARY KEY(BLOCK_NUMBER, CONTRACT_ADDRESS)
);

CREATE TABLE IF NOT EXISTS ETHEREUM.TOKENS(
  CONTRACT_ADDRESS VARCHAR NOT NULL,
  NAME VARCHAR,
  DECIMALS DECIMAL(78, 0) NOT NULL,
  SYMBOL VARCHAR,
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP NOT NULL,
  PRIMARY KEY(BLOCK_NUMBER, CONTRACT_ADDRESS)
);

CREATE TABLE IF NOT EXISTS ETHEREUM.NFT_COLLECTIONS(
  CONTRACT_ADDRESS VARCHAR NOT NULL,
  NAME VARCHAR,
  TOKEN_STANDARD VARCHAR,
  SYMBOL VARCHAR,
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP NOT NULL,
  PRIMARY KEY(BLOCK_NUMBER, CONTRACT_ADDRESS)
);

CREATE TABLE IF NOT EXISTS ETHEREUM.NFTS(
  CONTRACT_ADDRESS VARCHAR NOT NULL,
  TOKEN_ID DECIMAL(78, 0) NOT NULL,
  TIME_STAMP TIMESTAMP NOT NULL,
  TOKEN_URI VARCHAR,
  BLOCK_NUMBER BIGINT NOT NULL,
  PRIMARY KEY(BLOCK_NUMBER, CONTRACT_ADDRESS, TOKEN_ID)
);

CREATE TABLE IF NOT EXISTS ETHEREUM.NATIVETOKEN_TRANSFERS(
  TRANSACTION_HASH VARCHAR NOT NULL,
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP,
  FROM_ VARCHAR,
  TO_ VARCHAR,
  VALUE_ DECIMAL(78, 0),
  PRIMARY KEY(BLOCK_NUMBER, TRANSACTION_HASH)
);

CREATE TABLE IF NOT EXISTS ETHEREUM.ERC20_EVT_TRANSFER(
  TRANSACTION_HASH VARCHAR NOT NULL,
  EVENT_INDEX INT NOT NULL,
  BLOCK_NUMBER BIGINT,
  TIME_STAMP TIMESTAMP,
  FROM_ VARCHAR,
  TO_ VARCHAR,
  VALUE_ DECIMAL(78, 0),
  CONTRACT_ADDRESS VARCHAR,
  PRIMARY KEY(BLOCK_NUMBER, TRANSACTION_HASH, EVENT_INDEX)
);

CREATE TABLE IF NOT EXISTS ETHEREUM.ERC20_EVT_APPROVAL(
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP,
  TRANSACTION_HASH VARCHAR NOT NULL,
  EVENT_INDEX INT NOT NULL,
  OWNER VARCHAR,
  SPENDER VARCHAR,
  VALUE_ DECIMAL(78, 0),
  CONTRACT_ADDRESS VARCHAR,
  PRIMARY KEY(BLOCK_NUMBER, TRANSACTION_HASH, EVENT_INDEX)
);

CREATE TABLE IF NOT EXISTS ETHEREUM.ERC721_EVT_TRANSFER(
  TRANSACTION_HASH VARCHAR NOT NULL,
  EVENT_INDEX INT NOT NULL,
  TOKEN_ID DECIMAL(78, 0) NOT NULL,
  BLOCK_NUMBER BIGINT,
  TIME_STAMP TIMESTAMP,
  FROM_ VARCHAR,
  TO_ VARCHAR,
  CONTRACT_ADDRESS VARCHAR,
  PRIMARY KEY(BLOCK_NUMBER, TRANSACTION_HASH, EVENT_INDEX)
);

CREATE TABLE IF NOT EXISTS ETHEREUM.ERC721_EVT_APPROVAL(
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP,
  TRANSACTION_HASH VARCHAR NOT NULL,
  EVENT_INDEX INT NOT NULL,
  TOKEN_ID DECIMAL(78, 0) NOT NULL,
  OWNER VARCHAR,
  APPROVED VARCHAR,
  CONTRACT_ADDRESS VARCHAR,
  PRIMARY KEY(BLOCK_NUMBER, TRANSACTION_HASH, EVENT_INDEX)
);

CREATE TABLE IF NOT EXISTS ETHEREUM.ERC1155_EVT_TRANSFER(
  TRANSACTION_HASH VARCHAR NOT NULL,
  EVENT_INDEX INT NOT NULL,
  OPERATOR VARCHAR,
  BLOCK_NUMBER BIGINT,
  TIME_STAMP TIMESTAMP,
  FROM_ VARCHAR,
  TO_ VARCHAR,
  CONTRACT_ADDRESS VARCHAR,
  VALUE_ DECIMAL(78, 0),
  ID DECIMAL(78, 0),
  PRIMARY KEY(BLOCK_NUMBER, TRANSACTION_HASH, EVENT_INDEX)
);

CREATE TABLE IF NOT EXISTS ETHEREUM.ERC1155_EVT_TRANSFERBATCH(
  TRANSACTION_HASH VARCHAR NOT NULL,
  EVENT_INDEX INT NOT NULL,
  OPERATOR VARCHAR,
  BLOCK_NUMBER BIGINT,
  TIME_STAMP TIMESTAMP,
  FROM_ VARCHAR,
  TO_ VARCHAR,
  CONTRACT_ADDRESS VARCHAR,
  VALUES_ VARCHAR,
  IDS VARCHAR,
  PRIMARY KEY(BLOCK_NUMBER, TRANSACTION_HASH, EVENT_INDEX)
);

CREATE TABLE IF NOT EXISTS ETHEREUM.CONTRACT_EVT_APPROVALFORALL(
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP,
  TRANSACTION_HASH VARCHAR NOT NULL,
  EVENT_INDEX INT NOT NULL,
  OPERATOR VARCHAR,
  ACCOUNT VARCHAR,
  APPROVED BOOLEAN,
  CONTRACT_ADDRESS VARCHAR,
  PRIMARY KEY(BLOCK_NUMBER, TRANSACTION_HASH, EVENT_INDEX)
);

CREATE TABLE IF NOT EXISTS ETHEREUM.CONTRACT_EVT_OWNERSHIPTRANSFERRED(
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP,
  TRANSACTION_HASH VARCHAR NOT NULL,
  EVENT_INDEX INT NOT NULL,
  PREVIOUSOWNER VARCHAR,
  NEWOWNER VARCHAR,
  CONTRACT_ADDRESS VARCHAR,
  PRIMARY KEY(BLOCK_NUMBER, TRANSACTION_HASH, EVENT_INDEX)
);

CREATE TABLE IF NOT EXISTS ETHEREUM.NATIVE_WALLETS(
  WALLET_ADDRESS VARCHAR NOT NULL,
  BLOCK_NUMBER BIGINT NOT NULL,
  BALANCE DECIMAL(78, 0),
  TIME_STAMP TIMESTAMP,
  PRIMARY KEY(WALLET_ADDRESS, BLOCK_NUMBER)
);

CREATE TABLE IF NOT EXISTS ETHEREUM.FUNGIBLETOKEN_WALLETS(
  WALLET_ADDRESS VARCHAR NOT NULL,
  TOKEN_ADDRESS VARCHAR NOT NULL,
  BLOCK_NUMBER BIGINT NOT NULL,
  BALANCE DECIMAL(78, 0),
  TIME_STAMP TIMESTAMP,
  PRIMARY KEY(WALLET_ADDRESS, TOKEN_ADDRESS, BLOCK_NUMBER)
);

CREATE TABLE IF NOT EXISTS ETHEREUM.ERC721_OWNERS(
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP,
  CONTRACT_ADDRESS VARCHAR NOT NULL,
  TOKEN_ID DECIMAL(78, 0) NOT NULL,
  OWNER VARCHAR,
  BALANCE DECIMAL(78, 0),
  PRIMARY KEY(BLOCK_NUMBER, CONTRACT_ADDRESS, TOKEN_ID)
);

CREATE TABLE IF NOT EXISTS ETHEREUM.ERC1155_OWNERS(
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP,
  CONTRACT_ADDRESS VARCHAR NOT NULL,
  TOKEN_ID DECIMAL(78, 0) NOT NULL,
  OWNER VARCHAR,
  BALANCE DECIMAL(78, 0),
  PRIMARY KEY(BLOCK_NUMBER, CONTRACT_ADDRESS, TOKEN_ID, OWNER)
);

CREATE TABLE IF NOT EXISTS ETHEREUM.STORAGE_SLOTS(
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP,
  TRANSACTION_HASH VARCHAR NOT NULL,
  TRANSACTION_INDEX INT,
  CONTRACT_ADDRESS VARCHAR NOT NULL,
  SLOT_POSITION VARCHAR NOT NULL,
  SLOT_VALUE VARCHAR,
  PRIMARY KEY(BLOCK_NUMBER, CONTRACT_ADDRESS)
);

CREATE TABLE IF NOT EXISTS UNISWAP_V2_ETHEREUM.UNISWAPV2_PRICE_FEED (
  BLOCK_NUMBER BIGINT NOT NULL,
  PAIR_ADDRESS VARCHAR NOT NULL,
  TIME_STAMP TIMESTAMP,
  TOKEN0_PRICE DECIMAL(200, 100),
  TOKEN1_PRICE DECIMAL(200, 100),
  TOKEN0_USD_PRICE DECIMAL(200, 100),
  TOKEN1_USD_PRICE DECIMAL(200, 100),
  TOTAL_LIQUIDITY_USD DECIMAL(200, 100),
  PRIMARY KEY(BLOCK_NUMBER, PAIR_ADDRESS)
);

CREATE TABLE IF NOT EXISTS UNISWAP_V3_ETHEREUM.UNISWAPV3_PRICE_FEED (
  BLOCK_NUMBER BIGINT NOT NULL,
  POOL_ADDRESS VARCHAR NOT NULL,
  TIME_STAMP TIMESTAMP,
  TOKEN0_PRICE DECIMAL(200, 100),
  TOKEN1_PRICE DECIMAL(200, 100),
  TOKEN0_USD_PRICE DECIMAL(200, 100),
  TOKEN1_USD_PRICE DECIMAL(200, 100),
  POOL_LIQUIDITY_USD DECIMAL(200, 100),
  TOKEN0_TOTALVALUE_LOCKED DECIMAL(200, 100),
  TOKEN1_TOTALVALUE_LOCKED DECIMAL(200, 100),
  PRIMARY KEY(BLOCK_NUMBER, POOL_ADDRESS)
);

CREATE TABLE IF NOT EXISTS UNISWAP_V2_ETHEREUM.UNISWAPV2_PAIR (
  PAIR_ADDRESS VARCHAR NOT NULL,
  PAIR_NAME VARCHAR,
  TOKEN0_ADDRESS VARCHAR,
  TOKEN1_ADDRESS VARCHAR,
  PAIR_DECIMAL DECIMAL(78, 0),
  PAIR_SYMBOL VARCHAR,
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP,
  PRIMARY KEY(BLOCK_NUMBER, PAIR_ADDRESS)
);

CREATE TABLE IF NOT EXISTS UNISWAP_V3_ETHEREUM.UNISWAPV3_POOL (
  POOL_ADDRESS VARCHAR NOT NULL,
  TOKEN0_ADDRESS VARCHAR,
  TOKEN1_ADDRESS VARCHAR,
  POOL_FEE SMALLINT,
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP,
  PRIMARY KEY(BLOCK_NUMBER, POOL_ADDRESS)
);

CREATE TABLE IF NOT EXISTS AAVE_V2_ETHEREUM.LENDINGPOOLCONFIGURATORV2_EVT_RESERVEINTERESTRATESTRATEGYCHANGED (
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP,
  TRANSACTION_HASH VARCHAR NOT NULL,
  EVENT_INDEX INT NOT NULL,
  ASSET VARCHAR,
  STRATEGY VARCHAR,
  CONTRACT_ADDRESS VARCHAR,
  PRIMARY KEY(BLOCK_NUMBER, TRANSACTION_HASH, EVENT_INDEX)
);

CREATE TABLE IF NOT EXISTS AAVE_V2_ETHEREUM.LENDINGPOOLCONFIGURATOR_EVT_RESERVEINTERESTRATESTRATEGYCHANGED (
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP,
  TRANSACTION_HASH VARCHAR NOT NULL,
  EVENT_INDEX INT NOT NULL,
  ASSET VARCHAR,
  STRATEGY VARCHAR,
  CONTRACT_ADDRESS VARCHAR,
  PRIMARY KEY(BLOCK_NUMBER, TRANSACTION_HASH, EVENT_INDEX)
);

CREATE TABLE IF NOT EXISTS AAVE_V2_ETHEREUM.MORPHO_EVT_WITHDRAWN (
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP,
  TRANSACTION_HASH VARCHAR NOT NULL,
  EVENT_INDEX INT NOT NULL,
  _SUPPLIER VARCHAR NOT NULL,
  _RECEIVER VARCHAR NOT NULL,
  _POOL_TOKEN VARCHAR NOT NULL,
  _AMOUNT DECIMAL(78, 0),
  _BALANCE_ON_POOL DECIMAL(78, 0),
  _BALANCE_IN_P2P DECIMAL(78, 0),
  CONTRACT_ADDRESS VARCHAR,
  PRIMARY KEY(BLOCK_NUMBER, TRANSACTION_HASH, EVENT_INDEX)
);

CREATE TABLE IF NOT EXISTS AAVE_V2_ETHEREUM.MORPHO_EVT_BORROWED (
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP,
  TRANSACTION_HASH VARCHAR NOT NULL,
  EVENT_INDEX INT NOT NULL,
  _BORROWER VARCHAR NOT NULL,
  _POOL_TOKEN VARCHAR NOT NULL,
  _AMOUNT DECIMAL(78, 0),
  _BALANCE_ON_POOL DECIMAL(78, 0),
  _BALANCE_IN_P2P DECIMAL(78, 0),
  CONTRACT_ADDRESS VARCHAR,
  PRIMARY KEY(BLOCK_NUMBER, TRANSACTION_HASH, EVENT_INDEX)
);

CREATE TABLE IF NOT EXISTS AAVE_V2_ETHEREUM.MORPHO_EVT_SUPPLIED (
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP,
  TRANSACTION_HASH VARCHAR NOT NULL,
  EVENT_INDEX INT NOT NULL,
  _FROM VARCHAR NOT NULL,
  _ON_BEHALF VARCHAR NOT NULL,
  _POOL_TOKEN VARCHAR NOT NULL,
  _AMOUNT DECIMAL(78, 0),
  _BALANCE_ON_POOL DECIMAL(78, 0),
  _BALANCE_IN_P2P DECIMAL(78, 0),
  CONTRACT_ADDRESS VARCHAR,
  PRIMARY KEY(BLOCK_NUMBER, TRANSACTION_HASH, EVENT_INDEX)
);

CREATE TABLE IF NOT EXISTS AAVE_V2_ETHEREUM.MORPHO_EVT_REPAID (
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP,
  TRANSACTION_HASH VARCHAR NOT NULL,
  EVENT_INDEX INT NOT NULL,
  _REPAYER VARCHAR NOT NULL,
  _ON_BEHALF VARCHAR NOT NULL,
  _POOL_TOKEN VARCHAR NOT NULL,
  _AMOUNT DECIMAL(78, 0),
  _BALANCE_ON_POOL DECIMAL(78, 0),
  _BALANCE_IN_P2P DECIMAL(78, 0),
  CONTRACT_ADDRESS VARCHAR,
  PRIMARY KEY(BLOCK_NUMBER, TRANSACTION_HASH, EVENT_INDEX)
);

CREATE TABLE IF NOT EXISTS AAVE_V2_ETHEREUM.MORPHO_EVT_LIQUIDATED (
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP,
  TRANSACTION_HASH VARCHAR NOT NULL,
  EVENT_INDEX INT NOT NULL,
  _LIQUIDATOR VARCHAR NOT NULL,
  _LIQUIDATED VARCHAR NOT NULL,
  _POOL_TOKEN_BORROWED VARCHAR NOT NULL,
  _AMOUNT_REPAID DECIMAL(78, 0),
  _POOL_TOKEN_COLLATERAL VARCHAR NOT NULL,
  _AMOUNT_SEIZED DECIMAL(78, 0),
  CONTRACT_ADDRESS VARCHAR,
  PRIMARY KEY(BLOCK_NUMBER, TRANSACTION_HASH, EVENT_INDEX)
);

CREATE TABLE IF NOT EXISTS AAVE_V2_ETHEREUM.MORPHO_EVT_P2PINDEXCURSORSET (
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP,
  TRANSACTION_HASH VARCHAR NOT NULL,
  EVENT_INDEX INT NOT NULL,
  _POOL_TOKEN VARCHAR NOT NULL,
  _NEW_VALUE INT,
  CONTRACT_ADDRESS VARCHAR,
  PRIMARY KEY(BLOCK_NUMBER, TRANSACTION_HASH, EVENT_INDEX)
);

CREATE TABLE IF NOT EXISTS AAVE_V2_ETHEREUM.MORPHO_EVT_MARKETCREATED (
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP,
  TRANSACTION_HASH VARCHAR NOT NULL,
  EVENT_INDEX INT NOT NULL,
  _POOL_TOKEN VARCHAR NOT NULL,
  _RESERVE_FACTOR INT,
  _P2P_INDEX_CURSOR INT,
  CONTRACT_ADDRESS VARCHAR,
  PRIMARY KEY(BLOCK_NUMBER, TRANSACTION_HASH, EVENT_INDEX)
);

CREATE TABLE IF NOT EXISTS COMPOUND_V2_ETHEREUM.CTOKEN_INTEREST_RATES (
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP,
  RESERVE VARCHAR,
  SUPPLY_RATE_PER_BLOCK DECIMAL(39, 0),
  BORROW_RATE_PER_BLOCK DECIMAL(39, 0),
  SUPPLY_TVL DECIMAL(39, 0),
  BORROW_TVL DECIMAL(39, 0),
  EXCHANGE_RATE_STORED DECIMAL(39, 0),
  PRIMARY KEY(BLOCK_NUMBER, RESERVE)
);

CREATE TABLE IF NOT EXISTS COMPOUND_V3_ETHEREUM.CTOKEN_INTEREST_RATES (
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP,
  RESERVE VARCHAR,
  SUPPLY_RATE DECIMAL(39, 0),
  BORROW_RATE DECIMAL(39, 0),
  UTILIZATION_RATE DECIMAL(39, 0),
  SUPPLY_TVL DECIMAL(39, 0),
  BORROW_TVL DECIMAL(39, 0),
  PRIMARY KEY(BLOCK_NUMBER, RESERVE)
);

CREATE TABLE IF NOT EXISTS AAVE_V2_ETHEREUM.INTEREST_RATES (
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP,
  RESERVE VARCHAR,
  A_TOKEN VARCHAR,
  V_TOKEN VARCHAR,
  VARIABLEBORROWRATE DECIMAL(39, 0),
  STABLEBORROWRATE DECIMAL(39, 0),
  LIQUIDITYRATE DECIMAL(39, 0),
  SUPPLY_TVL DECIMAL(39, 0),
  BORROW_TVL DECIMAL(39, 0),
  PRIMARY KEY(BLOCK_NUMBER, RESERVE)
);

CREATE TABLE IF NOT EXISTS AAVE_V3_ETHEREUM.INTEREST_RATES (
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP,
  RESERVE VARCHAR,
  A_TOKEN VARCHAR,
  V_TOKEN VARCHAR,
  VARIABLEBORROWRATE DECIMAL(39, 0),
  STABLEBORROWRATE DECIMAL(39, 0),
  LIQUIDITYRATE DECIMAL(39, 0),
  SUPPLY_TVL DECIMAL(39, 0),
  BORROW_TVL DECIMAL(39, 0),
  PRIMARY KEY(BLOCK_NUMBER, RESERVE)
);

CREATE TABLE IF NOT EXISTS SPARK_ETHEREUM.INTEREST_RATES (
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP,
  RESERVE VARCHAR,
  A_TOKEN VARCHAR,
  V_TOKEN VARCHAR,
  VARIABLEBORROWRATE DECIMAL(39, 0),
  STABLEBORROWRATE DECIMAL(39, 0),
  LIQUIDITYRATE DECIMAL(39, 0),
  SUPPLY_TVL DECIMAL(39, 0),
  BORROW_TVL DECIMAL(39, 0),
  PRIMARY KEY(BLOCK_NUMBER, RESERVE)
);

CREATE TABLE IF NOT EXISTS COMPOUND_V2_ETHEREUM.ORACLE_PRICE_FEEDS (
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP,
  RESERVE VARCHAR,
  PRICE Decimal(39, 0),
  ORACLE_ADDRESS VARCHAR,
  PRIMARY KEY(BLOCK_NUMBER, RESERVE)
);

CREATE TABLE IF NOT EXISTS COMPOUND_V3_ETHEREUM.ORACLE_PRICE_FEEDS (
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP,
  RESERVE VARCHAR,
  PRICE Decimal(39, 0),
  ORACLE_ADDRESS VARCHAR,
  PRIMARY KEY(BLOCK_NUMBER, RESERVE)
);

CREATE TABLE IF NOT EXISTS AAVE_V2_ETHEREUM.ORACLE_PRICE_FEEDS (
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP,
  RESERVE VARCHAR,
  PRICE Decimal(39, 0),
  ORACLE_ADDRESS VARCHAR,
  PRIMARY KEY(BLOCK_NUMBER, RESERVE)
);

CREATE TABLE IF NOT EXISTS AAVE_V3_ETHEREUM.ORACLE_PRICE_FEEDS (
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP,
  RESERVE VARCHAR,
  PRICE Decimal(39, 0),
  ORACLE_ADDRESS VARCHAR,
  PRIMARY KEY(BLOCK_NUMBER, RESERVE)
);

CREATE TABLE IF NOT EXISTS SPARK_ETHEREUM.ORACLE_PRICE_FEEDS (
  BLOCK_NUMBER BIGINT NOT NULL,
  TIME_STAMP TIMESTAMP,
  RESERVE VARCHAR,
  PRICE Decimal(39, 0),
  ORACLE_ADDRESS VARCHAR,
  PRIMARY KEY(BLOCK_NUMBER, RESERVE)
);