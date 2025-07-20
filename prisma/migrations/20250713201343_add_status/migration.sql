-- CreateEnum
CREATE TYPE "ReplStatus" AS ENUM ('RUNNING', 'STOPPED');

-- AlterTable
ALTER TABLE "Repl" ADD COLUMN     "status" "ReplStatus" NOT NULL DEFAULT 'RUNNING';
