import { HardhatUserConfig } from "hardhat/config";
import "@nomicfoundation/hardhat-toolbox";
import "hardhat-gas-reporter";
import "dotenv/config";
import '@openzeppelin/hardhat-upgrades';

const config: HardhatUserConfig = {
  gasReporter: {
    enabled: false,
  },
  solidity: {
    compilers: [
      {
        version: "0.8.18",
        settings: {
          optimizer: {
            enabled: true, // Default: false
            runs: 200, // Default: 200,
          },
          viaIR: true,
        },
      },
    ],
  },
  networks: {
    hardhat: {
    },
    bsctest: {
      gas: 4100000,
      gasPrice: 8000000000,
      url: "https://bsc-testnet.blockpi.network/v1/rpc/public",
      chainId: 97,
      accounts: [`${process.env.WALLET_KEY}`]
    },
    bsc: {
      url: "https://bsc-dataseed.binance.org",
      chainId: 56,
      accounts: [`${process.env.WALLET_KEY}`]
    }
  }
};

export default config;
