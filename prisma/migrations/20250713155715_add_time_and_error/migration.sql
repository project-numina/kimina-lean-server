/*
  Warnings:

  - Added the required column `time` to the `Proof` table without a default value. This is not possible if the table is not empty.

*/
-- AlterTable
ALTER TABLE "Proof" ADD COLUMN     "error" TEXT,
ADD COLUMN     "time" DOUBLE PRECISION NOT NULL;
